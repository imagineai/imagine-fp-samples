Compi
=====

En este trabajo describimos la implementación de un compilador para
un lenguaje imperativo con clases, abordando las distintas etapas que
intervienen en el desarrollo: análisis léxico, parsing, análisis estático,
generación de código intermedio y por último código de máquina.

La implementación fue realizada en Haskell, siguiendo una modularización
que pretende respetar la división en etapas del desarrollo de compiladores.

# Dependencias

* base       >= 4.7.0
* parsec     >= 3.1.0
* containers >= 0.6.0
* mtl        >= 2.2.0
* pretty     >= 1.1.3.6
* filepath   >= 1.4.0
* process    >= 1.6.5.0

# Instalación

### Usando *stack* (Recomendado)

1. `stack setup`
2. `stack build`

### Usando cabal

1. `cabal configure`
2. `cabal build`
3. `cabal install`

### Usando GHC

`ghc --make Main`

# Uso utilizando stack

```
$stack exec -- compi [opciones]

Optiones: 

  -i <entrada>  --input=<entrada>  Nombre del archivo de <entrada>
  -o <salida>   --output=<salida>  Renombra el archivo ejecutable a <salida>
  -t <etapa>    --target=<etapa>   <etapa> es la de "parse", "staticcheck",
     				   "codinter", "assembly" o "executable".
                                   La compilación procede hasta la etapa dada.
  -h            --help             Muestra la información actual.
```

# Ejemplos

* Ejemplos/Ejemplo1.compi: Ejemplo variado para mostrar el parseo.
* Ejemplos/Ejemplo2.compi: Ejemplo para mostrar la localidad.
* Ejemplos/selectionSort.compi: Una implementación andando del selección
  sort que utiliza atributos de clase, varias funciones definidas y uso
  de funciones externas.
