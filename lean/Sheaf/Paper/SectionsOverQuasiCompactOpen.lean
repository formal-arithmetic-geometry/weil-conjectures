module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Grp.Colimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
universe u
/-! # Sections over a quasi-compact open in an affine scheme
Source: literature/stacks-project/properties.tex, Lemma 01PM
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open-in-affine)
-/
/-- The affine sections calculation of Properties, Lemma 01PM.
The diagrams are presentations of the two Hom systems: `r` is the inclusion of
ideal powers and `q` is the quotient projection. Their transition maps are
restriction, and restriction followed by projection, respectively. The natural
transformations `c` and `c'` express compatibility with all transitions. Their
basic-open restrictions are the fractions phi(f^n)/f^n and y/f^n, using the
literal fraction section `StructureSheaf.const`; the latter holds for every lift y.
The conclusions concern the induced colimit maps, not the disjoint unions.

Source: Stacks Project, Properties, Lemma 01PM.
Proof: Cover D by the basic opens of a finite generating set of I. Localized
fractions glue uniquely, since linearity makes their values equal on overlaps;
changing a quotient lift changes the numerator by an element killed by f^n.
Multiplying numerator and denominator by f proves transition compatibility.
For injectivity, a section that vanishes has its finitely many numerators killed
by a common power of the generators. A sufficiently high power of I lies in
the ideal of those powers, so restriction of the homomorphism is zero. This
proves injectivity in both colimits. For surjectivity of the quotient comparison,
write a section with a common denominator exponent on the finite basic-open
cover. Increase that exponent until the overlap relations hold in M. Sending
powers of the generators to the numerators is well-defined modulo their common
annihilator; a high power of I lies in the ideal they generate, and its
annihilator contains that common annihilator. The resulting map into M/N_n
represents the given section. Finally, if Ix = 0 implies x = 0, induction gives
N_n = 0 for all n, identifying the two systems and comparisons.
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open-in-affine)
-/
theorem sections_over_quasiCompactOpen_of_affine
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (I : Ideal A) (hIfg : I.FG)
    (D : (Spec (CommRingCat.of A)).Opens)
    (hD : ∀ (p : PrimeSpectrum A), p ∈ D ↔ ¬ ∀ a : A, a ∈ I → a ∈ p.asIdeal)
    (N : ℕ → Submodule A M)
    (hN : ∀ n x, x ∈ N n ↔ ∀ a : A, a ∈ I ^ n → a • x = 0) :
    ∃ (r : ∀ (n m : ℕ), n ≤ m →
        (ModuleCat.of A (I ^ m : Ideal A) ⟶ ModuleCat.of A (I ^ n : Ideal A)))
      (q : ∀ (n m : ℕ), n ≤ m →
        (ModuleCat.of A (M ⧸ N n) ⟶ ModuleCat.of A (M ⧸ N m)))
      (F G : ℕ ⥤ AddCommGrpCat.{u})
      (e : ∀ n, F.obj n ≅ AddCommGrpCat.of
        (ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A M))
      (e' : ∀ n, G.obj n ≅ AddCommGrpCat.of
        (ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A (M ⧸ N n)))
      (c : F ⟶ (Functor.const ℕ).obj
        (AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D)))
      (c' : G ⟶ (Functor.const ℕ).obj
        (AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D))),
      (∀ (n m : ℕ) (h : n ≤ m) (x : (I ^ m : Ideal A)),
        (r n m h x : A) = (x : A)) ∧
      (∀ (n m : ℕ) (h : n ≤ m) (x : M),
        q n m h ((N n).mkQ x) = (N m).mkQ x) ∧
      (∀ (n m : ℕ) (h : n ≤ m)
        (φ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A M),
        (e m).hom (F.map (homOfLE h) ((e n).inv φ)) = r n m h ≫ φ) ∧
      (∀ (n m : ℕ) (h : n ≤ m)
        (ψ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A (M ⧸ N n)),
        (e' m).hom (G.map (homOfLE h) ((e' n).inv ψ)) = r n m h ≫ ψ ≫ q n m h) ∧
      (∀ (f : A) (hf : f ∈ I), ∃ hle : PrimeSpectrum.basicOpen f ≤ D,
        (∀ (n : ℕ) (φ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A M),
          (tilde (R := CommRingCat.of A) (ModuleCat.of A M)).presheaf.map (homOfLE hle).op
              (c.app n ((e n).inv φ)) =
            StructureSheaf.const (R := A) (φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩)
              (f ^ n) (PrimeSpectrum.basicOpen f)
              (fun p hp ↦ p.asIdeal.primeCompl.pow_mem hp n)) ∧
        (∀ (n : ℕ)
          (ψ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A (M ⧸ N n))
          (y : M), (N n).mkQ y = ψ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ →
          (tilde (R := CommRingCat.of A) (ModuleCat.of A M)).presheaf.map (homOfLE hle).op
              (c'.app n ((e' n).inv ψ)) =
            StructureSheaf.const (R := A) y (f ^ n) (PrimeSpectrum.basicOpen f)
              (fun p hp ↦ p.asIdeal.primeCompl.pow_mem hp n))) ∧
      Function.Injective (colimit.desc F
        ⟨AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D), c⟩) ∧
      Function.Bijective (colimit.desc G
        ⟨AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D), c'⟩) ∧
      ((∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) →
        Function.Bijective (colimit.desc F
          ⟨AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D), c⟩)) := by sorry

end AlgebraicGeometry
