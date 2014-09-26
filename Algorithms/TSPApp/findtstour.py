'''
Written for Coursera course "Algorithms: Design and Analysis, Part 2"
Programming assignment for Week 5
Created on Aug 11, 2014

Solves the (NP-hard) Traveling Salesman Problem using Euclidean distances
between cities. Takes data in a text file, with the number of cities
on the first line and the x- and y-coordinates (separated by spaces
or tabs) of a city on each subsequent line.

This assumes that the two cities which are closest together must
be next to each other on the minimum cost tour. (One is used as the
"source" city; the other is considered its "buddy.")
This calculates two sets of minimal half-paths starting at the source
city (see below), then joins them to complete a tour.
 - Half-paths that go directly from the source city to its buddy, then
     continue through other cities.
 - Half-paths that do not contain the buddy city.
'''

import argparse
from math import sqrt, log, ceil
from time import time

INF = float('inf')

class TSP():
    def __init__(self, coords = None, n = -1):
        self.distances = {}
        self.min_paths = {}
        self.cities_by_index = []
        self.city_source = -1
        self.city_buddy = -1
        self.cityset_all_except_source = -1
        if n >= 0:
            self.set_n(n)
        if coords is not None:
            self.calc_pairwise_distances(coords)
    
    def set_n(self, n):
        self.n = n
        # Using powers of two to represent cities, so "cities_by_index[i]"
        # represents the city with index i and has a value of 2**i (or 1<<i).
        self.cities_by_index = [1 << i for i in range(self.n)]
    
    def calc_pairwise_distances(self, coords):
        '''Take a list of cities' x- and y-coordinates (one tuple per city)
        and compute all pairwise distances. Also determine which two cities
        are closest together. (They will be kept adjacent in the tour.)
        '''
        min_path = INF
        if self.n == -1:
            self.set_n(len(coords))
        
        for index_i in range(self.n):
            city_i = self.cities_by_index[index_i]
            x_i, y_i = coords[index_i]
            for index_j in range(index_i + 1, self.n):
                city_j = self.cities_by_index[index_j]
                x_j, y_j = coords[index_j]
                
                # Compute Euclidean distance between cities with indexes i and j.
                dist = sqrt((x_i - x_j) ** 2 + (y_i - y_j) ** 2)
                self.distances[city_i + city_j] = dist
                if dist < min_path:
                    min_path = dist
                    self.city_source, self.city_buddy = city_i, city_j
        
        # Store for later use in finding complementary paths.
        self.cityset_all_except_source = sum(self.cities_by_index) - self.city_source

    def get_buddy_cities(self):
        '''Return the indexes of the two cities that are closest together.'''
        if self.city_source >= 0 and self.city_buddy >= 0:
            return self._index_of(self.city_source), self._index_of(self.city_buddy)

    def calc_min_tour_from_coords(self):
        '''Calculate the lengths of half-paths in two complementary sets.
        Then join the paths (to form complete tours) and return the tour
        with the minimal total distance.
        '''
        min_tour = INF
        paths1 = self._calc_half_paths(True)
        paths2 = self._calc_half_paths(False)
        
        # target1 is the final city on a half-path from paths1, which passes
        # through all cities in cityset1 and has a total distance of distance1.
        # Similarly, target2 is the final city on a half-path from paths2,
        # which passes through the cities in cityset2 and has a total distance
        # of paths2[target2][cityset2].
        for target1 in paths1:
            for (cityset1, distance1) in paths1[target1].items():
                cityset2 = self._find_complementary_path(cityset1)
                for target2 in self._cities_in_set(cityset2):
                    if target2 != self.city_source:
                        # Total tour distance is the lengths of half-paths through
                        # cityset1 and cityset2 plus the distance between their
                        # final cities (target1 and target2, respectively).
                        tour = (distance1 + paths2[target2][cityset2] +
                                         self._get_dist(target1, target2))
                        if tour < min_tour:
                            min_tour = tour
        return min_tour
    
    def _calc_half_paths(self, incl_buddy):
        '''Calculate and return minimal half-paths starting at the source city.
        If incl_buddy is True, then the path will go immediately to the buddy
        city from source. Otherwise, the path will not pass through buddy at all. 
        '''
        base_last_city = self.city_buddy if incl_buddy else self.city_source
        base_cityset = self.city_source | base_last_city
        base_path = self._get_dist(self.city_source, base_last_city)
        min_paths_prev = None

        for set_of_citysets in self._calc_larger_subsets(base_cityset):
            min_paths = {city: {} for city in self.cities_by_index}
            for cityset in set_of_citysets:
                if not min_paths_prev:
                    target = cityset - base_cityset
                    min_paths[target][cityset] = (base_path +
                                                 self._get_dist(base_last_city, target))
                else:
                    # For each target city, iterate through possible penultimate
                    # cities to find the shortest path to the target (of those
                    # that pass through the given cityset).
                    targets = self._cities_in_set(cityset - base_cityset)
                    for target in targets:
                        min_path = INF
                        for penult_city in targets:
                            if penult_city != target:
                                # Total distance of the path to target is the 
                                # length of the shorter path to penult_city
                                # (excluding target from cityset), plus the
                                # distance between penult_city and target.
                                path = (min_paths_prev[penult_city][cityset - target]
                                        + self._get_dist(penult_city, target))
                                if path < min_path:
                                    min_path = path
                        min_paths[target][cityset] = min_path
            min_paths_prev = min_paths
        
        # Return dict of dicts, indexed by target city, then by the path's cityset.
        return min_paths
    
    def _get_dist(self, city_i, city_j):
        '''Look up and return the distance between two cities.''' 
        return 0 if city_i == city_j else self.distances[city_i + city_j]
    
    def _calc_larger_subsets(self, base_cityset):
        '''Yield a set consisting of all the citysets that contain one city
        more than the previous citysets.
        '''
        smaller_citysets = [base_cityset]
        base_size = self._count_cities_in_set(base_cityset)
        subset_size = base_size + 1
        
        # The right side of this inequality is equivalent to (n+1)/2 if n is odd,
        # n/2 if n is even and the base contains only the source city, and
        # n/2 + 1 if n is even and the base contains both the source city and its buddy.
        while subset_size <= ceil((self.n - base_size) / 2) + 1:
            set_of_citysets = set()
            for cityset in smaller_citysets:
                for city in self._cities_not_in_set(cityset | self.city_buddy):
                    set_of_citysets.add(cityset + city)
            yield set_of_citysets
            smaller_citysets = set_of_citysets
            subset_size += 1
    
    def _cities_in_set(self, cityset):
        '''Return a list of all the cities contained in the given cityset.'''
        return [city for city in self.cities_by_index if cityset & city]
    
    def _cities_not_in_set(self, cityset):
        '''Return a list of all the cities NOT in the given cityset.'''
        return [city for city in self.cities_by_index if not cityset & city]

    def _count_cities_in_set(self, cityset):
        '''Return the number of cities contained in the given set of cityset.'''
        return bin(cityset).count('1')
    
    def _find_complementary_path(self, cityset):
        '''Return a cityset containing the source city plus all cities
        that are not in the given cityset, i.e., all the cities
        needed on a path that is complementary to cityset.
        '''
        return cityset ^ self.cityset_all_except_source
    
    def _index_of(self, city):
        '''Return the original index of the given city.'''
        return int(log(city, 2))

def load_coords(filename):
    '''Read a file containing the number of cities on the first line and
    the x- and y-coordinates of a city on each subsequent line.
    Return coords, a list of (x, y) tuples, and the number of cities, n.
    '''
    coords = []
    file = open(filename)
    n = int(file.readline())
    for line in file:
        x, y = line.split()
        coords.append((float(x), float(y)))
    file.close()
    return coords, n

def main(filename):
    start_time = time()
    tsp = TSP(*load_coords(filename))
    print('Finding the shortest tour passing through the first %s cities in '
          '"%s."' % (tsp.n, filename))
    print('Nearest cities: City %s and City %s' % tsp.get_buddy_cities())
    print('Length of shortest tour:', round(tsp.calc_min_tour_from_coords(), 1))
    
    s = time() - start_time
    print('Time: %s seconds' % round(s, 2))
    if s >= 100:
        m, s = divmod(s, 60)
        print('  or: %s minutes, %s seconds' % (int(m), round(s, 2)))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Finds the shortest tour that'
                                     'passes through each city exactly once.')
    parser.add_argument('filename', nargs='?', default='AlgoTSP.txt')
    
    args = parser.parse_args()
    main(args.filename)

'''Results for AlgoTSP.txt
17 cities    Answer: 22953.64400554132    Total time: 1.23 seconds
18 cities    Answer: 23005.21706993607    Total time: 2.87 seconds
19 cities    Answer: 23101.93990866834    Total time: 6.67 seconds
20 cities    Answer: 23328.99036691422    Total time: 15.58 seconds
21 cities    Answer: 24146.20523053687    Total time: 35.35 seconds
22 cities    Answer: 24474.90366987281    Total time: 79.82 seconds
23 cities    Answer: 24522.41147834959    Total time: 177.23 seconds
24 cities    Answer: 26391.71263970836    Total time: 394.68 seconds
'''