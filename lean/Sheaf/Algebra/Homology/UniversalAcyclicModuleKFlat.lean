/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Sheaf.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Universal tensor acyclicity implies K-flatness

Source: Stacks Project, More on Algebra, Tag 0E8F,
`lemma-universally-acyclic-K-flat`, specialized to commutative rings
(blueprint: lem-sfb-universal-acyclic-module-kflat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CochainComplex

/-- If tensoring an arbitrary module complex with every finitely presented module
in degree zero is acyclic, the complex is K-flat. There is no boundedness or
termwise flatness hypothesis.

Source: Stacks Project, More on Algebra, Tag 0E8F,
`lemma-universally-acyclic-K-flat`
(blueprint: lem-sfb-universal-acyclic-module-kflat).

Proof:
1. Filtered colimits of acyclic module complexes are acyclic: represent a cycle
   at one stage, pass to a later stage where its differential vanishes, and use
   acyclicity there to obtain a primitive. Use
   lem-weil-pbc-filtered-colimit-modules-elementwise.
2. Total tensor commutes with degreewise directed colimits. Tensor commutes with
   colimits by lem-weil-pbc-tensor-commutes-with-colimits, and coproducts commute
   with colimits. The comparison preserves both signed differential terms.
3. Express any module as a directed colimit of finitely presented modules using
   lem-trf-module-finitely-presented-directed-colimit. Steps 1 and 2 extend the
   hypothesis to every module. Interchange the degree-zero module and the other
   factor; this introduces no sign.
4. A complex supported in one degree has acyclic total tensor by step 3: shifting
   only multiplies the differential by a sign and reindexes the degrees. The
   zero complex also has zero tensor.
5. Induct on the length of a finite supporting interval. The brutal truncation
   sequence separating its bottom degree is split degreewise, so remains exact
   after tensoring and totalization. Apply the homology long exact sequence
   lem-weil-pbc-complex-ses-homology-long-exact and the induction hypothesis.
6. Any bounded-above complex is the degreewise directed colimit of its bounded
   brutal lower truncations. Steps 1, 2 and 5 prove tensor acyclicity for it;
   acyclicity of the brutal truncations themselves is unnecessary.
7. Any complex is the degreewise directed colimit of its canonical upper
   truncations: in the top degree use the kernel of the outgoing differential.
   At each fixed degree the system is eventually constant. Steps 1, 2 and 6
   give tensor acyclicity for an arbitrary complex.
8. In particular the total tensor with every acyclic complex is acyclic, exactly
   def-pc-module-kflat-complex. The recorded predicate expresses the equivalent
   preservation of quasi-isomorphisms on both sides, by cones and symmetry. -/
theorem kFlat_of_acyclic_tensor_finitePresentation
    {A : Type u} [CommRing A] (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (hE : ∀ (M : ModuleCat.{u} A), Module.FinitePresentation A M →
      (mapBifunctor E
        ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj M)
        (curriedTensor (ModuleCat.{u} A))).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat E := by
  sorry

end CochainComplex
