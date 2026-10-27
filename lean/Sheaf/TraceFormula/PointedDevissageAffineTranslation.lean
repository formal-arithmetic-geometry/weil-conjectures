/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.PointedAffineDevissage
public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Affine sections of a pointed scheme devissage

Source: Stacks Project, flat.tex, Tags 05I0 (remark-same-notion) and 05HX
(definition-complete-devissage-algebra)
(blueprint: lem-trf-pointed-devissage-affine-translation).

The entry accessor only unpacks the given recursive chain. The conclusion retains its
rings, modules, ranks, ring maps, presentation maps, and free-module maps through explicit
identifications with global sections. Heterogeneous equalities accommodate the definitional
identification of the next entry's input with the preceding cokernel.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.PointedAffineDevissage

/-- An unpacked entry, used only to project the data already present in a chain.
Source: Stacks Project, Tag 05I0, affine sections of the diagrams in Tag 05HH
(blueprint: lem-trf-pointed-devissage-affine-translation). -/
structure Entry (B : Scheme.{u}) where
  X : Scheme.{u}
  f : X ⟶ B
  F : X.Modules
  x : X
  datum : PointedAffineOneStep f F x
  rank : ℕ
  alpha : SheafOfModules.free (R := datum.Y.ringCatSheaf) (ULift.{u} (Fin rank)) ⟶
    (Scheme.Modules.pushforward datum.π).obj datum.G

/-- Read the specified entry without choosing any new scheme or morphism.
Source: Stacks Project, Tag 05I0, the finite sequence of affine diagrams
(blueprint: lem-trf-pointed-devissage-affine-translation). -/
@[irreducible]
noncomputable def entry {B X : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
    (c : PointedAffineDevissage B f F x n) : Fin n → Entry B :=
  match c with
  | .nil _ _ _ _ _ _ _ _ => Fin.elim0
  | .cons s r α _ tail => Fin.cases ⟨_, _, _, _, s, r, α⟩ (entry tail)

/-- Global sections of the given presentation isomorphism, using the identity-on-elements
pushforward section identification.
Source: Stacks Project, Tags 05I0 and 01HV
(blueprint: lem-trf-pointed-devissage-affine-translation). -/
noncomputable def Entry.presentationSection {B : Scheme.{u}} (e : Entry B) :
    Γ(e.datum.G, ⊤) → Γ(e.F, ⊤) :=
  e.datum.presentation.hom.app ⊤

/-- Global sections of the quotient map of the actual alpha in the chain.
Source: Stacks Project, Tags 05I0 and 01IC
(blueprint: lem-trf-pointed-devissage-affine-translation). -/
noncomputable def Entry.quotientSection {B : Scheme.{u}} (e : Entry B) :
    Γ(e.datum.G, ⊤) → Γ((cokernel e.alpha : e.datum.Y.Modules), ⊤) :=
  (cokernel.π e.alpha).val.app (op ⊤)

/-- The image of a standard basis section under the given alpha, evaluated on the top open.
Source: Stacks Project, Tags 05I0 and 05HH
(blueprint: lem-trf-pointed-devissage-affine-translation). -/
noncomputable def Entry.basisSection {B : Scheme.{u}} (e : Entry B) :
    Fin e.rank → Γ(e.datum.G, ⊤) :=
  fun k ↦ (SheafOfModules.freeHomEquiv _ e.alpha ⟨k⟩).val (op ⊤)

/-- The precise affine-section identifications for a complete algebra devissage.
The two ring equivalences preserve the base-ring actions; the additive equivalence is
semilinear for the displayed coordinate-ring equivalence. Alpha is checked on the standard
basis, which determines the entire linear map, including rank zero. The initial and successive
presentation squares retain the given sheaf isomorphisms, not merely their isomorphism classes.
Source: Stacks Project, Tags 05I0 and 05HX
(blueprint: lem-trf-pointed-devissage-affine-translation). -/
def IsAffineSections
    (R S : CommRingCat.{u}) [Algebra R S] [Algebra.FiniteType R S]
    (N : ModuleCat.{u} S) [Module.Finite S N] (q : PrimeSpectrum S) (n : ℕ)
    (c : PointedAffineDevissage (Spec R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (tilde N) q n)
    (D : CompleteAlgebraDevissage R S (Ideal.comap (algebraMap R S) q.asIdeal) N) : Prop :=
  ∃ (length : D.n = n)
    (coordinateA : ∀ i : Fin D.n, D.A i ≃+* Γ((c.entry (Fin.cast length i)).datum.Z, ⊤))
    (coordinateB : ∀ i : Fin D.n, D.B i ≃+* Γ((c.entry (Fin.cast length i)).datum.Y, ⊤))
    (module : ∀ i : Fin D.n, D.M i ≃+ Γ((c.entry (Fin.cast length i)).datum.G, ⊤))
    (rank : ∀ i : Fin D.n, D.rIndex i = (c.entry (Fin.cast length i)).rank),
    (∀ (i : Fin D.n) (a : R), coordinateA i (algebraMap R (D.A i) a) =
      ((c.entry (Fin.cast length i)).datum.π ≫
        (c.entry (Fin.cast length i)).datum.g).appTop ((Scheme.ΓSpecIso R).inv a)) ∧
    (∀ (i : Fin D.n) (a : R), coordinateB i (algebraMap R (D.B i) a) =
      (c.entry (Fin.cast length i)).datum.g.appTop ((Scheme.ΓSpecIso R).inv a)) ∧
    (∀ (i : Fin D.n) (a : D.A i) (m : D.M i),
      module i (a • m) = coordinateA i a • module i m) ∧
    (∀ (i : Fin D.n) (a : D.B i), coordinateA i (D.bToA i a) =
      (c.entry (Fin.cast length i)).datum.π.appTop (coordinateB i a)) ∧
    (∀ (i : Fin D.n) (hi : i.val = 0),
      HEq (((coordinateA i).toRingHom.comp (D.sToA i hi).toRingHom).comp
        (Scheme.ΓSpecIso S).hom.hom) (c.entry (Fin.cast length i)).datum.i.appTop.hom) ∧
    (∀ (i j : Fin D.n) (hij : j.val = i.val + 1),
      HEq (((coordinateA j).toRingHom.comp (D.bToAnext i j hij).toRingHom).comp
        (coordinateB i).symm.toRingHom) (c.entry (Fin.cast length j)).datum.i.appTop.hom) ∧
    (∀ (i : Fin D.n) (k : Fin (D.rIndex i)),
      module i (D.alpha i (Pi.single k 1)) =
        (c.entry (Fin.cast length i)).basisSection (Fin.cast (rank i) k)) ∧
    (∀ (i : Fin D.n) (hi : i.val = 0),
      HEq (fun m : N ↦ (c.entry (Fin.cast length i)).presentationSection
        (module i (D.firstIso i hi m))) (fun m : N ↦ tilde.toOpen N ⊤ m)) ∧
    (∀ (i j : Fin D.n) (hij : j.val = i.val + 1),
      HEq (fun m : D.M i ↦ (c.entry (Fin.cast length j)).presentationSection
        (module j (D.cokerIso i j hij (Submodule.Quotient.mk m))))
        (fun m : D.M i ↦ (c.entry (Fin.cast length i)).quotientSection (module i m)))

/-- Affine sections convert the given pointed chain to a complete algebra devissage,
with the same length, ranks, and actual diagram, including its residue-field maps.

Source: Stacks Project, Tags 05I0 and 05HX
(blueprint: lem-trf-pointed-devissage-affine-translation).

Proof plan:
1. Apply the affine-spectrum dictionary to the ring maps in each datum. The closed-immersion
criterion and finite-presentation criterion give the surjective finitely presented maps;
finiteness of the finite morphism and the affine finite-type module criterion give the finite
algebras and modules. Smoothness and geometric irreducibility are retained.
2. Finite pushforward preserves quasi-coherence. The affine tilde/Gamma adjunction and the
pushforward section identification turn each alpha into its actual section map; its values
on the free basis are precisely those in the basis comparison in `IsAffineSections`.
3. The quasi-coherent cokernel/image formula identifies successive section quotients with
the sections of the next module, compatibly with the given presentation isomorphisms.
The first presentation and the tilde unit give the initial module isomorphism. The last
sheaf cokernel is zero, so its section quotient is zero.
4. The affine fibre ring is the base change by the residue field of the base prime. Smooth
fibres are geometrically reduced, and geometric irreducibility makes this fibre nonempty
and integral, so its coordinate ring is a nonzero domain.
5. Smoothness makes the coordinate algebra flat. Its quotient by the extended base prime
is flat over the base domain, hence torsion-free. It therefore injects into the fibre ring,
its localization at the nonzero base elements. The extended prime is consequently prime,
and the fibre's generic point maps to exactly that prime.
6. The tilde stalk-localization formula identifies the stipulated generic residue map with
the tensor of the actual section map. On fractions the identification sends
`(m/s) tensor l` to `m tensor (s-bar)^{-1} l`; the inverse sends `m tensor l` to
`(m/1) tensor l`. They commute with alpha, including rank zero. Tensor symmetry translates
this to the left tensor convention of `CompleteAlgebraDevissage.residue_bijective`.
7. Assemble these conditions and the displayed section identifications. If the chain has
length zero, its sheaf is zero; the tilde unit gives a zero initial module, so the empty
algebra devissage satisfies the zero-case condition. No support-dimension equalities enter.
-/
theorem exists_affineSections
    (R S : CommRingCat.{u}) [Algebra R S] [Algebra.FiniteType R S]
    (N : ModuleCat.{u} S) [Module.Finite S N] (q : PrimeSpectrum S) (n : ℕ)
    (c : PointedAffineDevissage (Spec R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (tilde N) q n) :
    ∃ D : CompleteAlgebraDevissage R S (Ideal.comap (algebraMap R S) q.asIdeal) N,
      IsAffineSections R S N q n c D := by
  sorry

end AlgebraicGeometry.PointedAffineDevissage
