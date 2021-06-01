While
======

# Dependencies

### Installing dependencies with *cabal*

`cabal install --only-dependencies`

# 1

### Using cabal

0. `cabal clean`
1. `cabal configure`
2. `cabal build`
3. `cabal install`

### Using GHC

`ghc --make src/Main`

# While kind-files

# Usage

#### Starting the interpreter
```sh
$> iwhile
		--- WHILE intérprete, versión 0.1 ---
		          (help for info)

[--,--] > 
```
The prompt is conformed with two components (initially empty), where the left component tells the loaded program and the right componen the loaded data.

#### Loading a program
We can load a program using **lp** (load program)
```sh
[--,--] > lp examples/sum1.while
[sum1,--] > 
```
So, for instance, we load the program `sum1.while` that adds one.

#### Loading a data
We can load a data using **ld** (load data). This command has three different uses:

- Loading a data of type `nat`, `tree` or `list`.
    ```sh
    [sum1,--] > ld 1
    [sum1,data] > 
    ```
- Loading a data from a file with extension `.data`.
    ```sh
    [sum1,--] > ld examples/1.data
    [sum1,data] > 
    ```
- Loading a program as a data.
    ```sh
    [sum1,--] > ld examples/sum1.while
    [sum1,sum1] > 
    ```

#### Using iwhile
It's possible to run a previously loaded while program with a data doing **run**, followed by the type on which we want to represent the result. These could be
any of the followings, clearly not all the results supports all the type representations.

- `tree`
    ```sh
          |   
          |   
         ---  
        /   \ 
       nil nil
    ```
- `data`
    ```sh
    (nil . nil)
    ```
- `nat`
    ```sh
    1
    ```
- `list`
    ```sh
    (nil)
    ```
- `prog`
    ```
    read 1
        1 := cons nil 1
    write 1
    ```
Following with the example on which we had loaded the program that adds one and the data was the number 1:

```sh
[sum1,data] > run nat 
Result:

2
```

#### Other useful commands

Also we have **showp** y **showd** commands that allows us to show a program or a data respectively. As it happens with **run** these have different
types of representation: `tree`, `data`, `nat`, `list` and `prog`.

Another useful command is **append**, that allows us to append two datas.

```sh
[--,--] > ld 1
[--,data] > append 2
[--,data.data] > showd tree 
Dato cargado: 

         |         
         |         
    ---------      
   /         \     
   |         |     
   |         |     
  ---     -----    
 /   \   /     \   
nil nil nil    |   
               |   
              ---  
             /   \ 
            nil nil
```
