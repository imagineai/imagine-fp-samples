{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

{-|
Module      : ImagineCompiler
Description : Imagine compiler main functions.
Copyright   : (c) 2020-2021 Imagine AI
License     : BSD-3-Clause
Maintainer  : sos@imagine.ai
Stability   : develop

-}

module ImagineCompiler (
  -- * Generate files for creating a new project for the given framework.
    create
  -- * Generate files from the given specification files.
  , compile

  -- * Framework type.
  , Framework(..)

  -- * Error type
  , Error
  ) where

import ImagineInput
import ImagineOutput
import StaticChecks

import ImagineMonad
import ImagineSettings
import Parser.ParserInputFiles (parseFWString)

import CodeGenerator

create :: AppEnvironment -> String -> ProjectName  ->
          Imagine OutputContent
create env fw name = parseFWString fw >>= generateInitCode env name

compile :: ImagineInput inp => inp -> Imagine OutputContent
compile input = parseImagineInput input >>= \is ->
                checkImagineSpec is >>
                generateCode is
