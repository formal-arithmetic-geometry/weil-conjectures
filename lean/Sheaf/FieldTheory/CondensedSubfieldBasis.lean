/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Coordinates of a finite subfield basis on condensed modules

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, first two sentences
(blueprint: lem-sfb-condensed-subfield-basis).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

/-- A finite field basis gives a coordinate homeomorphism and inverse internal condensed
module maps, with the prescribed formulas on every profinite set. The compatible algebra
structure expresses the inclusion of the two subfields in the fixed algebraic closure.
Finite biproduct projections identify the chosen finite free object's sections with tuples;
the sum of its injections represents a tuple in that object.

Source: blueprint main-20261015, lem-sfb-subfield-flat.proof.md, first two sentences
(blueprint: lem-sfb-condensed-subfield-basis).

Proof:
1. Over the complete nontrivially normed field Q_ell, F is finite dimensional and Hausdorff.
Each E-linear coordinate is Q_ell-linear, so
`lem-sfb-finite-dimensional-linear-map-continuous` makes it continuous. Their product is
continuous. This uses the induced topologies of `sk-def-sfb-condensed-ring`.
2. The inverse sends a tuple to the finite sum of basis vectors times its coordinates.
The subfield inclusion and multiplication are continuous. The basis identities show both
composites are identities, giving the displayed homeomorphism.
3. On continuous functions, postcompose with these coordinates and use the same finite
sum for the inverse. Both operations commute with precomposition along maps of profinite
sets and are additive. Thus they are inverse morphisms of abelian sheaves.
4. The actions are pointwise multiplication, componentwise on tuples. The ordinary tensor
universal property and `def-weil-pbc-sheafification` descend these actions to the sheafified
tensor of `sk-def-sfb-sheaf-tensor`; its strong monoidality gives the module axioms of
`sk-def-sfb-module-objects`. These are the existing regular and restricted regular modules.
5. E-linearity of the coordinates and of the basis sum makes both maps action-compatible
on pure tensors. Additivity and uniqueness of sheafification extend this compatibility to
the sheaf tensors. The sectionwise inverse identities then give the internal module iso.
-/
theorem exists_condensedSubfieldBasisIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    [Algebra E F] [IsScalarTower E F (PadicAlgCl ℓ)]
    (n : ℕ) (b : Module.Basis (Fin n) E F) :
    ∃ c : F ≃ₜ (Fin n → E),
      (∀ (s : F) (i : Fin n), c s i = b.coord i s) ∧
      (∀ a : Fin n → E, c.symm a = ∑ i, algebraMap E F (a i) * b i) ∧
      ∃ (hι : Continuous (algebraMap E F))
        (e : (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (continuousMapRingSheafMap (algebraMap E F) hι))).obj
              (Mod.regular (continuousMapRingObj F)) ≅
                Mod.finiteFree (continuousMapRingObj E) n),
        (∀ (S : Profinite.{u}) (i : Fin n) (f : C(S, F)) (x : S),
          (((e.hom ≫ biproduct.π (fun _ : Fin n ↦
            Mod.regular (continuousMapRingObj E)) i).hom.hom.app (op S)
              (ULift.up f)).down x) = b.coord i (f x)) ∧
        (∀ (S : Profinite.{u}) (f : Fin n → C(S, E)) (x : S),
          ((e.inv.hom.hom.app (op S)
            (∑ i, (biproduct.ι (fun _ : Fin n ↦
              Mod.regular (continuousMapRingObj E)) i).hom.hom.app (op S)
                (ULift.up (f i)))).down x) =
                  ∑ i, algebraMap E F (f i x) * b i) := by
  sorry

end Profinite
