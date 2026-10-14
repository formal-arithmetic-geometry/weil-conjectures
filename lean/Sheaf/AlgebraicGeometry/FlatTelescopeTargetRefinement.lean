/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.Algebra.Homology.BoundedFlatReplacement

/-! # Refining one augmented tower against one flat telescope

Source: the finite-piece bar-enlargement argument of
`lem-sc-flat-telescope-arrow-bar-data`, with the source tower retained through a
levelwise quasi-isomorphism. Stacks Project 03EW, 077J and 06XX supply the resolving
class and bounded resolutions; the bar argument is an agent-written expansion.
(blueprint: lem-sc-flat-telescope-target-refinement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- A bounded flat tower augmented into one actual flat telescope can be refined,
levelwise by quasi-isomorphisms, to admit a strict map into a tower presenting that
one target up to homotopy. No truncation augmentations or second target are involved.

Source: finite-piece bar enlargement in the proof of
`lem-sc-flat-telescope-arrow-bar-data`; Stacks Project 03EW, 077J and 06XX.

Proof. First resolve the source tower by a generator-valued tower L with maps
v_n:L_n -> E_n. Take the resolving class to be sums of affine-open generators
j_{U!} O_U; 03EW supplies covers, and the bounded resolution argument underlying
077J applies to this class. At stage zero resolve the bounded-above complex E_0.
Suppose L_n and v_n are constructed. Form the bounded-above cone H of
L_n -> E_n -> E_(n+1), and choose a bounded-above generator resolution Q -> H.
Compose Q -> H -> L_n[1], and form its shifted cone L_(n+1). This realizes the
triangle L_n -> L_(n+1) -> Q -> L_n[1] with degreewise split first map and
cokernel Q. The triangle comparison with L_n -> E_(n+1) -> H -> L_n[1]
provides a map L_(n+1) -> E_(n+1) commuting up to homotopy with v_n;t_n.
Extend that homotopy degreewise along the split inclusion of L_n, and subtract
its boundary from the comparison map. The resulting map v_(n+1) commutes
strictly; it is a quasi-isomorphism by the triangle comparison since the other
two vertical maps are identity and Q -> H. No lifting through a sheaf epimorphism
is assumed. This is the cone induction of 06XX with E_(n+1) replacing a good
truncation; its final termwise-surjectivity addition is unnecessary here.
Choose the degreewise splittings so that old generator summands remain named.
Augment L_n into T by v_n;p_n. The upper bounds may increase with n, but any
finite initial segment has a common upper bound.

Each affine-open generator is compact for coproducts: its Hom functor is sections
on a quasi-compact affine open. A section has locally finite support in a sheaf
coproduct, hence finite support on that open. Close finite sets of named summands
of L_m under the differential upwards. Compactness gives finitely many new summands
at each step; boundedness above terminates the procedure. The resulting finite
subcomplexes have finitely many nonzero degrees. Let D_n be the filtered diagram
of such subcomplexes at stages m <= n, ordered by inclusion after transition.
Its colimit is L_n. Set R_n to the direct-sum total of the unnormalized bar diagram
of D_n, with simplicial degree p placed in cochain degree -p. The augmentation
c_n:R_n -> L_n -> E_n is a quasi-isomorphism. Indeed filtered colimits of module
sheaves are exact, so the horizontal augmented bar complex is exact; the common
upper bound at stage n makes each total diagonal finite after reindexing. The bar
inclusions give s_n and strictly satisfy s_n c_(n+1) = c_n t_n.

Write the supplied target as a telescope. Its finite cone blocks C_k use domain
indices <= k and codomain indices <= k+1. They are bounded above and flat, their
inclusions split degreewise, and their union is the target T. Each finite source
subcomplex maps into some C_k, because its finitely many compact generator terms
use only finitely many target summands. The factor is a chain map since C_k -> T
is monic. Adjoin the chain of C_k to the union D of the source diagrams, putting
an arrow x -> k exactly when the augmentation of x factors through C_k. The least
such k is monotone and is left adjoint to inclusion of the target chain. The unit
of this adjunction gives, by inserting its arrow in bar strings with alternating
signs, a bar homotopy equivalence with the target-chain bar construction.

Let F_n be the bar total of the full subdiagram on D_n and target indices <= n.
These terms are flat and bounded above. Inclusions define u and a:R -> F. Their
transition squares commute strictly, so their sum maps commute with 1-shift. The
union bar total has a degreewise split exact presentation by 1-shift on the sum
of the F_n: split the augmentation using each simplex's first stage, and solve
the finite-support recurrence for its kernel. The cone augmentation is a homotopy
equivalence by the split exact-sequence cone calculation. For the target chain,
compare its bar augmentation with the telescope augmentation: compare the bar
resolution of the constant right functor with its two-term representable resolution
by 1-shift. Both are projective resolutions, so successive lifts give comparison
maps and homotopies; tensor these with the diagram C_k.
Comparison homotopies use finite sums on each input, so totalization is legitimate.
Choose this comparison to lift identity on the augmented constant functor;
then tensoring makes its composite with the augmentation into T exactly the
bar augmentation. The telescope of the finite cone blocks maps homotopy
equivalently to T by the same split exact-sequence calculation. Thus the
canonical bar augmentation B(I) -> T itself is a homotopy equivalence: compose
with the target-chain inclusion, a homotopy equivalence by the unit-insertion
homotopy, and cancel that equivalence. Define r to be the canonical cone
augmentation Tel(F) -> B(I) -> T, rather than an arbitrary comparison map.
Its shifted restriction is zero and its unshifted restriction is the sum of
bar augmentations. Naturality gives the displayed equality with Sigma.desc(c_n;p_n).
Zero complexes and zero maps require no exception; include the zero subcomplex
as an initial source object when necessary. All witnesses are existential data.
(blueprint: lem-sc-flat-telescope-target-refinement). -/
theorem exists_flat_telescope_target_refinement (Y : Scheme.{u})
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, E n ⟶ T)
    (hp : ∀ n : ℕ, t n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ E n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ t n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      ∃ r : CochainComplex.mappingCone (flatTelescopeDifferential F u) ⟶ T,
        IsIso (Q.map r) ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential F u)).comp
          (Cochain.ofHom r) (add_zero _) = 0 ∧
        Limits.Sigma.map a ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential F u) ≫ r =
          Sigma.desc (fun n : ℕ ↦ c n ≫ p n) := by sorry

end AlgebraicGeometry
