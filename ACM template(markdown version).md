[TOC]

## 1 Base algorithm

### 1.1 Bisection method

search for $min(b),b\in\{a[k]\geq x\}$

``` cpp
while(l<r){
	int mid = (l + r) >> 1;
	if(a[mid] >= x) r = mid;
	else l = mid + 1;
}
return a[l];
```

search for $max(b),b\in\{a[k]\leq x\}$

```cpp
while(l<r){
	int mid = (l + r + 1) >> 1;
	if(a[mid] <= x) l = mid;
	else r = mid - 1;
}
return a[l];
```



## 2 Graph Theory and Network Algorithms

## 3 Algebraic Algorithms

## 4 Number Theory

## 5 Data structure

## 6 Computational geometry

## 7 Classic Problems

