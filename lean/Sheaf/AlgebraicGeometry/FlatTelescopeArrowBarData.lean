/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.FlatTruncationTower

/-! # Strict augmentation data from finite-piece bar diagrams

Source: Stacks Project Tags 03EW, 077J and 06XX for flat-generator resolutions;
the finite-piece and bar-enlargement argument below is an agent-written expansion
of the parent arrow-diagram construction, not a literal assertion of those tags.
(blueprint: lem-sc-flat-telescope-arrow-bar-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- Tower and target-augmentation data, before constructing a source-cone map.
The target augmentations have zero shifted component and agree strictly with the
source augmentation on the two sum maps. Neither a source-cone map nor an equality
of maps from the source cone is a conclusion.

Source: Stacks Project 03EW (flat generating covers), 077J and 06XX (the split
flat-generator truncation tower), and the parent construction steps 1--2. The bar
argument is supplied here, replacing the invalid whole-stage support argument.

Proof. Work on the affine-open basis of Y, transporting module sheaves back to the
Zariski site. For an affine open U let G_U = j_{U!} O_U. These are flat generators.
They are compact with respect to coproducts: Hom(G_U, M) = Gamma(U, M), and a section
of a sheaf coproduct has finite support locally; quasi-compactness of U makes its
support finite on all of U. This uses neither projectivity nor coherence of M.
Choose the section-indexed generating covers in 03EW using this basis. Apply the
construction of 077J/06XX with resolving class the sums of these G_U. It gives
bounded-above complexes L_n with terms sums of generators, quasi-isomorphisms
v_n : L_n -> truncLE(n,P), and degreewise split inclusions L_n -> L_(n+1) whose
cokernel terms are also sums of generators. Choose their degreewise splittings, so
old summands remain named summands at later stages. The maps v_n into P commute
strictly. This is the stronger generator-valued form of the truncation construction;
its existence is not inferred from a bare termwise-flat tower.

A finite set of named summands of L_n lies in a finite subcomplex: starting with
these summands, close under differential upwards. Each differential from a generator
has finite support by compactness, and the upper bound on L_n makes this process
terminate. A finite subcomplex therefore has finitely many nonzero degrees, finite
sums of generators in each degree, and a degreewise split inclusion into L_n. Such
subcomplexes form a filtered poset with union L_n. Let D_n consist of all pairs
(m,F) for m <= n and finite subcomplexes F of L_m; an arrow is inclusion after the
transition to a later stage. D_n is filtered: move two objects to stage n and close
the union of their finite sets under differential. Its colimit is L_n. The inclusions
D_n -> D_(n+1) and augmentations of their diagrams into P are strict.

Use the unnormalized simplicial replacement B(D): its p-simplices are the sum of
F(x_0) over strings x_0 -> ... -> x_p, with alternating faces and internal differential.
Use direct-sum totalization, placing the p-direction in cochain degree -p. Each
B(D_n) is bounded above by the maximum of the bounds on L_0,...,L_n, and all its
terms are flat. The bar augmentation B(D_n) -> L_n is a quasi-isomorphism: filtered
colimits of module sheaves are exact, so the horizontal bar homology is L_n in
degree zero and zero elsewhere. Reindexing the internal direction by its common
upper bound puts this bicomplex in the first quadrant; each total diagonal is finite,
so the usual successive-filtration argument applies without an unbounded-convergence
assumption. Set E0_n = B(D_n) and q_n to be this augmentation followed by v_n.
Functoriality supplies t0 and strict compatibility of q_n into P.

For each supplied telescope T, construct an increasing filtration C_k of T by
finite cone blocks. A block includes the domain summands of the one-minus-shift
map with indices <= k and the codomain summands with indices <= k+1. Restrict that
map and take its cone. Each C_k is bounded above and termwise flat, its inclusion
in C_(k+1) is degreewise a summand inclusion, and the union is the literal telescope
T. A map from a finite subcomplex F above into T factors through some C_k: there
are finitely many source degrees and each term is a finite sum of compact generators,
so its two cone coordinates use finitely many target summands. The factor is a chain
map since C_k -> T is monic. Apply this to F -> P and F -> P -> Pprime separately.
No assertion is made that L_n, or B(D_n), factors through a single C_k.

For each target j form the poset I_j by adjoining its chain C_k to D = union D_n.
Keep the arrows in D and in the target chain, and put an arrow x -> k precisely
when the map from its finite subcomplex factors through C_k. There are no arrows
back to D. Every x has a least such index rho_j(x). It is monotone along inclusions
in D, since restriction of a factorization is a factorization. Extend rho_j by the
identity on target indices. It is left adjoint to inclusion of the target chain:
rho_j(x) <= k iff x -> k. Its unit supplies a natural transformation from identity
to inclusion followed by rho_j. Inserting the unit arrow in each possible position
of a bar string, with alternating signs, gives the bar chain homotopy; the diagrams'
structure maps give its coefficients. Thus inclusion of the target chain induces a
homotopy equivalence of bar totals, compatible with their augmentations into T_j.

Let I_j,n be the full subposet with source objects in D_n and target indices <= n,
and set Ej_n = B(I_j,n). These stages have a common finite upper bound, since the
source bounds involve only L_0,...,L_n and the target bounds only C_0,...,C_n.
Flatness follows from coproduct flatness. Inclusion of D_n gives the two level maps;
all transition squares commute strictly. Hence their sum maps commute with 1-shift.
The union of these bar stages is B(I_j), and each inclusion is degreewise split by
its named simplex summands. The sequence sum Ej -> sum Ej -> B(I_j) is degreewise
split exact: for each simplex choose its first stage of appearance to split the last
map, and solve the finite-support recurrence for the kernel. The cone augmentation
Tel(Ej) -> B(I_j) is therefore a homotopy equivalence; the standard split-sequence
cone computation gives its homotopy inverse, even though the degreewise splittings
need not be chain maps.

Finally B(chain C_k) is homotopy equivalent to Tel(C_k). One explicit verification
uses the two-term resolution of the constant right functor on the ordered natural
numbers by sums of representables, whose map is 1-shift. The simplicial bar resolution
and this resolution are projective resolutions of the same constant functor; lifting
successively along their augmentations gives comparison maps and comparison
homotopies. Tensor them with C_k to obtain maps and homotopies of the direct-sum
totals. The comparison homotopies use finite sums on each input, so no convergence is
needed. The cone augmentation Tel(C_k) -> T_j is a homotopy equivalence by the same
degreewise split exact-sequence argument for the finite-block filtration. Composing
these equivalences proves that the canonical augmentation r_j : Tel(Ej) -> T_j is a
homotopy equivalence. Its shifted restriction is zero; its unshifted restriction is
the sum of the bar augmentations. Naturality on D_n proves the last two strict sum
identities. The construction also handles zero maps, identity maps, and the empty
scheme; the empty filtered diagrams may instead be given their zero subcomplex as
an initial object. All choices occur in this existential proof, not in a definition.
(blueprint: lem-sc-flat-telescope-arrow-bar-data). -/
theorem exists_flat_telescope_arrow_bar_data (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (_c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (_c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (r₁ : CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁) ⟶ P)
        (r₂ : CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂) ⟶ P')
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        IsIso (Q.map r₁) ∧ IsIso (Q.map r₂) ∧
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential E₁ t₁)).comp
          (Cochain.ofHom r₁) (add_zero _) = 0 ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential E₂ t₂)).comp
          (Cochain.ofHom r₂) (add_zero _) = 0 ∧
        Limits.Sigma.map a ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential E₁ t₁) ≫ r₁ =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ∧
        Limits.Sigma.map b ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential E₂ t₂) ≫ r₂ =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ≫ f := by sorry

end AlgebraicGeometry
