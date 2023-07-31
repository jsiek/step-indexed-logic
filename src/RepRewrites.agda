{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module RepRewrites where

open import StepIndexedLogic2

{-# REWRITE #pureᵒ≡ #-}
{-# REWRITE #×ᵒ≡ #-}
{-# REWRITE #⊎ᵒ≡ #-}
{-# REWRITE #→ᵒ≡ #-}
{-# REWRITE #∀ᵒ≡ #-}
{-# REWRITE #∃ᵒ≡ #-}
{-# REWRITE ▷ᵒ≡ #-}
{-# REWRITE #μᵒ≡ #-}
