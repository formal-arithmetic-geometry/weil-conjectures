/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Bounded-below direct image and quasi-coherence

Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Derived direct image of a bounded-below object with quasi-coherent cohomology
has quasi-coherent cohomology. No compactness of the target is required.
Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).

Proof:
1. Represent E by a strictly bounded-below complex, using the standard t-structure.
   Apply exists_truncationHypercohomology to the module direct-image functor.
   Identify its right derived functor with schemeDerivedDirectImage, since both
   are computed by K-injective resolutions. The E2 terms are R^p f_* H^j(E).
2. The qcqs higher-direct-image theorem (Tag 01XJ, lem-pc-finite-support-hi)
   makes these terms quasi-coherent. Negative p and j < a terms vanish.
3. Each later page is a kernel modulo an image. The quasi-coherent kernel and
   cokernel/image lemmas imply, by induction on the page, quasi-coherence of
   every page term. In total degree q only 0 <= p <= q-a occurs, and each
   term stabilizes at a finite page by the half-plane bounds.
4. The convergence theorem supplies a finite filtration of H^q(Rf_*E), with
   those stable terms as graded pieces. Start from its zero last step and use
   isQuasicoherent_of_shortExact successively to deduce quasi-coherence of all
   filtration steps, ending at H^q(Rf_*E). This applies to every integer q.
-/
theorem schemeDerivedDirectImage_preserves_QCoh_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a : ℤ) [E.IsGE a] :
    schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) := by sorry

end AlgebraicGeometry
