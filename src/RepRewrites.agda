{-# OPTIONS --without-K --rewriting --prop #-}

module RepRewrites where

open import StepIndexedLogic2

{-# REWRITE #⊤ᵒ≡⊤ #-}
{-# REWRITE #⊥ᵒ≡⊥ #-}
{-# REWRITE #pureᵒ≡ #-}
{-# REWRITE #×ᵒ≡ #-}
{-# REWRITE #⊎ᵒ≡ #-}
{-# REWRITE #→ᵒ≡ #-}
{-# REWRITE #∀ᵒ≡ #-}
{-# REWRITE #∃ᵒ≡ #-}
{-# REWRITE #▷ᵒ≡ #-}
{-# REWRITE #μᵒ≡ #-}
{-# REWRITE #letᵒ≡ #-}
