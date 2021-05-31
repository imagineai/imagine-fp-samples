While
======

# Dependencias

### Instalando dependencias usando *cabal*

`cabal install --only-dependencies`

# Instalación

### Usando cabal

0. `cabal clean`
1. `cabal configure`
2. `cabal build`
3. `cabal install`

### Usando GHC

`ghc --make src/Main`

# Tipos de archivos while

# Uso

#### Iniciando el interprete
```sh
$> iwhile
		--- WHILE intérprete, versión 0.1 ---
		          (help para ayuda)

[--,--] > 
```
El promp se constituye de dos campos (inicialmente vacíos), donde el lugar izquierdo indica el programa cargado y el derecho el dato, o entrada, para ejecutar ese programa.

#### Cargando un programa
Para cargar un programa while usamos **lp** (load program)
```sh
[--,--] > lp examples/sum1.while
[sum1,--] > 
```
Cargamos, por ejemplo, el programa `sum1.while` que suma uno.

#### Cargando un dato
Para cargar un dato usamos **ld** (load data). Este comando se puede usar de tres maneras:

- Para cargar un dato de tipo `nat`, `tree` o `list`.
    ```sh
    [sum1,--] > ld 1
    [sum1,dato] > 
    ```
- Para cargar un dato desde un archivo con extensión `.data`.
    ```sh
    [sum1,--] > ld examples/1.data
    [sum1,dato] > 
    ```
- Para cargar un programa como dato.
    ```sh
    [sum1,--] > ld examples/sum1.while
    [sum1,sum1] > 
    ```

#### Usando iwhile
Para ejecutar un programa while y en un dato previamente cargados podemos hacer **run** seguido de la forma en que queremos representar el resultado. Las cuales a modo de ejemplo pueden llegar a tener la siguiente "forma", donde no siempre vamos a poder ver a todo dato (o programa) con cualquier representación.

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
Continuando con el ejemplo donde teníamos cargado el programa que sumaba uno y como dato al número 1:

```sh
[sum1,dato] > run nat 
Resultado:

2
```

#### Otros comandos útiles

Además existen **showp** y **showd** que nos permiten mostrar un programa o dato respectivamente. Y al igual que con **run** tenemos las distintas "formas" de representación (`tree`, `data`, `nat`, `list`, `prog`).

Por otro lado un comando que suele ser útil en ciertas circunstancias es el **append**, que funciona parecido al **ld**. Pero cuya meta es pegar dos datos.

```sh
[--,--] > ld 1
[--,dato] > append 2
[--,dato.dato] > showd tree 
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

# Ejemplos
