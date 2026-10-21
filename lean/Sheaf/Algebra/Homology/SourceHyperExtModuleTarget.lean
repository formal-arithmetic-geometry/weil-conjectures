/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # Source hyper-Ext with a module as target

Source: Stacks Project, Injectives, Tag 0G20, remark-spectral-sequences-ext-variant,
with target N[0]; Homology, Tags 0130 and 0132.
(blueprint: lem-trf-source-hyperext-module-target).

Ordinary A-modules are presented on the existing one-object identity-covering site.
Pages, limiting terms and abutment filtrations are in ModuleCat A, so all maps and
all identifications are A-linear. Ext uses Mathlib's small Ext and its scalar action.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Evaluate H^t RHom_A(K,N[0]) at the unique object of the ring site.
This is the ordinary cohomology A-module, using the recorded internal Hom functor.
Source: Stacks Project, Injectives, Tag 0G20, remark-spectral-sequences-ext-variant
(blueprint: lem-trf-source-hyperext-module-target). -/
noncomputable abbrev sourceHyperExtAbutment
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (RingSiteModules A)]
    (K : DerivedCategory (RingSiteModules A)) (N : RingSiteModules A) (t : ℤ) :
    ModuleCat.{u} A :=
  ModuleCat.of A
    (((homologyFunctor (RingSiteModules A) t).obj
      ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
        (CochainComplex.onePointRingSheaf A)).obj
          (op K, (singleFunctor (RingSiteModules A) 0).obj N))).val.obj (op ⟨PUnit.unit⟩))

/-- The source hyper-Ext spectral sequence for a bounded-above source and a module target.
The page isomorphisms in E give the kernel/image formula. The compatible isomorphisms
at each sufficiently late page express stabilization to E-infinity via the canonical
cycle and homology maps. The finite abutment filtration is indexed by the first degree;
putting i=t-j gives precisely the successive quotients with -b <= j <= t.

Source: Stacks Project, Injectives, Tag 0G20, remark-spectral-sequences-ext-variant;
Homology, Tags 0130 and 0132
(blueprint: lem-trf-source-hyperext-module-target).

Proof:
1. Replace a representative C of K by its upper canonical truncation at b, using
   def-sbc-standard-tstructure-derived-category (Tag 0118). Since H^a(K)=0 for a>b,
   the truncation inclusion is a quasi-isomorphism. Write M for this representative,
   with M^a=0 for a>b.
2. By lem-weil-pbc-ring-modules-enough-injectives, recursively embed C^0=N into I^0,
   put C^{r+1}=coker(C^r -> I^r), and embed C^{r+1} into I^{r+1}. The differential
   is I^r -> C^{r+1} -> I^{r+1}; extend by zero in negative degrees. Its degree-zero
   kernel is N and ker(d^r)=im(d^{r-1}) for r>0, so this is the injective resolution
   of def-sp-injective-resolutions (Tag 013K).
3. Lem-weil-pbc-bounded-below-injectives-kinjective (Tag 070J) makes I K-injective.
   Def-pur-derived-internal-hom computes RHom(K,N[0]) by T=Hom-complex(M,I), with
   the differential of def-pur-hom-complex. On the one-object identity-covering site,
   sheaf modules and sheaf Hom are ordinary A-modules and Hom_A (Tag 0G1Z).
4. Set D^{i,c}=Hom_A(M^{b-c},I^i) for i,c>=0, zero otherwise. Let d_I be
   postcomposition by d_I^i and d_II(f)=(-1)^{c-b+1} f composed with d_M^{b-c-1}.
   The differentials square to zero and commute. In T^t only -t<=a<=b contribute,
   so its product is the finite sum Tot(D)^{t+b}, with a=b-c and i=a+t.
   The total source-precomposition sign is (-1)^{i+c-b+1}=(-1)^{t+1}, exactly
   -(-1)^t in the Hom differential. Thus H^t(T)=H^{t+b}(Tot D), by degree
   translation with the same differential (def-sp-double-complex-total, Tag 012X).
5. For fixed i, put a=b-c, Z^a=ker d_M^a and B^a=im d_M^{a-1}. A cocycle
   M^a -> I^i kills B^a and restricts to Hom_A(Z^a/B^a,I^i). Every such map extends
   over M^a/B^a by injectivity. A cocycle whose restriction is zero factors through
   M^a/Z^a=B^{a+1}; extending over M^{a+1} writes it as a boundary, up to the
   invertible sign. At c=0, M^{b+1}=0 makes Z^b=M^b and the same argument applies.
   Hence H_II^c(D^{i,*})=Hom_A(H^{b-c}(K),I^i), A-linearly and compatibly with d_I
   (def-sp-injective-resolutions, Tag 0G20).
6. Apply thm-sp-double-complex-spectral-sequences (Tag 0130) in Mod(A). Step 5
   identifies its E1 with Hom_A(H^{b-c}(K),I^i), and E2 with Ext_A^i(H^{b-c}(K),N),
   by def-pur-derived-internal-hom and lem-sc-rhom-cohomology-ext-ring. These maps
   are A-linear: scalar multiplication is postcomposition by the scalar on I.
   Def-sp-spectral-sequence gives the next-page kernel/image identifications.
7. Reindex c=j+b. The differential keeps degree (s,1-s), and support becomes
   i>=0, j>=-b. The first-quadrant convergence theorem in Step 6 (Tag 0132)
   gives compatible stabilization isomorphisms and the first image filtration:
   F^0=H, F^{t+b+1}=0, gr^i=E-infinity^{i,t-i}, 0<=i<=t+b. By Step 4 this
   is the filtration on H^t RHom(K,N[0]) of def-sp-filtration. Equivalently its
   quotients are E-infinity^{t-j,j} for -b<=j<=t. If t+b<0, Tot(D) is zero in
   that degree, hence so is the abutment. No finiteness or Noetherian assumption
   on A, K or N was used. -/
theorem exists_source_hyperExt_module_target
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (RingSiteModules A)]
    (K : DerivedCategory (RingSiteModules A)) (N : RingSiteModules A) (b : ℤ)
    (hK : ∀ a : ℤ, b < a → IsZero ((homologyFunctor (RingSiteModules A) a).obj K)) :
    ∃ E : E₂CohomologicalSpectralSequence (ModuleCat.{u} A),
    ∃ EInf : ℤ → ℤ → ModuleCat.{u} A,
    ∃ F : ∀ t : ℤ, DecreasingFiltration (sourceHyperExtAbutment A K N t),
      (∀ (i : ℕ) (j : ℤ), Nonempty
        ((E.page 2).X ((i : ℤ), j) ≅ ModuleCat.of A
          (Abelian.Ext
            (ModuleCat.of A (((homologyFunctor (RingSiteModules A) (-j)).obj K).val.obj
              (op ⟨PUnit.unit⟩)))
            (ModuleCat.of A (N.val.obj (op ⟨PUnit.unit⟩))) i))) ∧
      (∀ (s : ℤ) (hs : 2 ≤ s) (i j : ℤ),
        i < 0 ∨ j < -b → IsZero ((E.page s hs).X (i, j))) ∧
      (∀ i j : ℤ, ∃ r : ℤ, ∃ _hr : 2 ≤ r,
        ∃ e : ∀ (s : ℤ) (hs : 2 ≤ s) (hrs : r ≤ s),
          (E.page s hs).X (i, j) ≅ EInf i j,
        ∀ (s : ℤ) (hs : 2 ≤ s) (hrs : r ≤ s) (hs' : 2 ≤ s + 1) (hrs' : r ≤ s + 1),
          (E.page s hs).iCycles (i, j) ≫ (e s hs hrs).hom =
            (E.page s hs).homologyπ (i, j) ≫ (E.iso s (s + 1) (i, j) rfl hs).hom ≫
              (e (s + 1) hs' hrs').hom) ∧
      (∀ t : ℤ, (F t).IsFinite ∧ (F t).IsExhaustive ∧ (F t).IsSeparated ∧
        (F t).F 0 = ⊤ ∧ (F t).F (t + b + 1) = ⊥ ∧
        ∀ j : ℤ, -b ≤ j → j ≤ t → Nonempty ((F t).gr (t - j) ≅ EInf (t - j) j)) ∧
      (∀ t : ℤ, t < -b → IsZero (sourceHyperExtAbutment A K N t)) := by
  sorry

end DerivedCategory
