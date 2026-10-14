/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Zariski's main theorem: compatibility imports

Source: Stacks Project, Algebra, Tags 00PK, 00PL and 00Q9
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away).

The duplicate Sheaf declaration has been removed. Callers transport their open
fibre singleton through `PrimeSpectrum.preimageHomeomorphFiber`, obtain the
`Algebra.QuasiFiniteAt` instance with Mathlib's
`Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber`, and apply
`Algebra.ZariskisMainProperty.of_finiteType` directly. This module preserves its
public imports for compatibility; no caller needs to import it for a proof.
-/

@[expose] public section
