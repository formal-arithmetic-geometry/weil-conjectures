/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli
public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
import Sheaf.AlgebraicGeometry.AffineGroupoidEtaleInvariantComparison
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Gluing

/-! # Stabilizer-preserving étale maps over affine groupoid moduli

Source: Stacks Project, stacks-more-morphisms.tex, Tags 0DUS, 0DUQ and 0DUR;
stacks-morphisms.tex, Tags 0DUB, 0CIM, 0CIN, 050F and 050K
(blueprint: lem-sfb-etale-stabilizer-preserving-affine-moduli).

The invariant-spectrum map is characterized by its specified restriction to the atlas.
The canonical comparison of the descended square retains both projections and its
2-isomorphism. Stabilizers are tested on every scheme, including nonreduced schemes.
The final two theorems state the composition and arbitrary stack base-change clauses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separated étale stabilizer-preserving morphisms descend over the invariant spectrum.
The resulting morphism is uniform categorical, qcqs, a universal homeomorphism, and
bijective on geometric isomorphism classes. Its target and maps are unique up to the
unique compatible scheme isomorphism.

Source: Stacks Project, Tag 0DUS, lemma-etale-separated-over-well-nigh-affine,
with Tags 0DUQ and 0DUR
(blueprint: lem-sfb-etale-stabilizer-preserving-affine-moduli).

Proof, following the eight steps of the DAG node:
1. Pull back the finite flat affine atlas U to G. Chartwise étale and separation
permanence make V separated étale over U. The separated étale space theorem makes
V a scheme; the locally quasi-finite finite-set lemma supplies affine neighbourhoods.
The pulled-back finite locally free groupoid Q presents G by fppf stackification.
Its finite orbits have invariant affine neighbourhoods, giving open quotient charts.
2. The endpoint squares are cartesian by association of 2-fibre products. The
stabilizer square is cartesian because h bijects all automorphism sheaves. Apply
lem-sfb-affine-groupoid-etale-invariant-comparison to each invariant affine chart;
quotient base change gives the corresponding cartesian square of stacks. Apply
lem-sfb-finite-flat-affine-groupoid-moduli to its vertical invariant-spectrum map.
3. Universal homeomorphisms identify overlap opens. Uniform categorical uniqueness
produces mutually inverse overlap maps, compatible with the map to M.
4. On triple overlaps categorical uniqueness proves the cocycle identity and the
required identities between overlap opens. Glue the schemes and their maps to M,
and glue the stack maps on scheme tests. The local cartesian comparisons glue.
5. Each affine atlas-to-moduli map is integral by
lem-a1-affine-groupoid-integral-invariants, hence universally closed. These local
maps give a surjective universally closed V to M'. The composite V to M is separated.
Use lem-weil-pbc-surjective-universally-closed-separated to deduce separation of u.
6. The vertical map is a base change of the original invariant-spectrum map.
Quasi-compactness and quasi-separatedness follow by base change, including for the
diagonal. Further 2-base changes give homeomorphisms of point spaces. Geometric
fibres retain exactly the original isomorphism classes. Flat maps to M' compose
with the étale u to flat maps to M, giving the uniform categorical property.
7. Any second uniform categorical square factors uniquely through this one and
conversely. Precomposition with the categorical maps makes both composites the
identity and proves compatibility with u. The cartesian comparison is fixed by its
projections and the specified 2-isomorphism, so this also gives uniqueness of squares.
8. The remaining two theorems state permanence under composition and base change;
their automorphism argument is given below. Empty schemes and variable ranks are allowed.
-/
theorem exists_etale_stabilizerPreserving_affine_moduli
    (k E L : Type u) [Field k] [CommRing E] [CommRing L]
    [Algebra k E] [Algebra k L] (σ τ : E →ₐ[k] L)
    (e : Spec (.of E) ⟶ Spec (.of L)) (i : Spec (.of L) ⟶ Spec (.of L))
    (c : pullback (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (Spec.map (CommRingCat.ofHom τ.toRingHom)) ⟶ Spec (.of L))
    [(Spec.map (CommRingCat.ofHom σ.toRingHom)).IsFiniteLocallyFree]
    [(Spec.map (CommRingCat.ofHom τ.toRingHom)).IsFiniteLocallyFree]
    (F : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (a : BasedFunctor (discreteModuli (yoneda.obj
      ((Spec (.of E)).asOver (Spec (.of k))))) F)
    (P : SchemeGroupoidQuotientPresentation
      ((Spec.map (CommRingCat.ofHom σ.toRingHom)).asOver (Spec (.of k)))
      ((Spec.map (CommRingCat.ofHom τ.toRingHom)).asOver (Spec (.of k))) e i c F a)
    (hF : IsAlgebraicModuliStack F)
    (f : BasedFunctor F (discreteModuli (yoneda.obj (affineGroupoidModuliBase σ τ))))
    (hf : a.comp f = discreteModuliMap (yoneda.map (affineGroupoidModuliAtlasMap σ τ)))
    (G : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hG : IsAlgebraicModuliStack G) (h : BasedFunctor G F)
    (hrep : IsRepresentableByAlgebraicSpaces h) (het : IsEtaleModuliMap h)
    (hsep : ModuliSchemeTest @IsProper (moduliRelativeDiagonal h))
    (hst : ∀ (T : Over (Spec (.of k))) (x : Functor.Fiber G.p T),
      Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap h T).mapIso α)) :
    ∃ (M' : Over (Spec (.of k))) (u : M' ⟶ affineGroupoidModuliBase σ τ),
      IsSeparated u.left ∧ Etale u.left ∧
      ∃ f' : BasedFunctor G (discreteModuli (yoneda.obj M')),
        (∀ (B : AlgebraicSpace (Spec (.of k))) (b : B.obj.obj ⟶ yoneda.obj M'),
          (∀ (T : Over (Spec (.of k))) (j : yoneda.obj T ⟶ B.obj.obj),
            AlgebraicSpace.IsEtale j → Flat (yoneda.preimage (j ≫ b)).left) →
          ∀ Y : AlgebraicSpace (Spec (.of k)),
            Function.Bijective (fun g : B.obj.obj ⟶ Y.obj.obj ↦
              (moduliTwoFiberFst (discreteModuliMap b) f').comp (discreteModuliMap g))) ∧
        IsQuasiCompactAlgebraicModuliMap.{u, v₂, w₂, u, u + 1, v₃, w₃} f' ∧
        IsQuasiSeparatedAlgebraicModuliMap f' ∧
        (∀ (Z : BasedCategory.{max u v₂ v₃, max (u + 1) w₂ w₃} (Over (Spec (.of k))))
          (g : BasedFunctor Z (discreteModuli (yoneda.obj M'))),
          IsAlgebraicModuliStack Z →
            IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f'))) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (j : k →+* Ω),
          Function.Bijective ((moduliFiberMap f'
            (Over.mk (Spec.map (CommRingCat.ofHom j)))).mapSkeleton.obj)) ∧
        ∃ η : f'.comp (discreteModuliMap (yoneda.map u)) ≅ h.comp f,
          (moduliTwoFiberLift f' h η).toFunctor.IsEquivalence ∧
          ∀ (M'' : Over (Spec (.of k))) (u' : M'' ⟶ affineGroupoidModuliBase σ τ)
            (f'' : BasedFunctor G (discreteModuli (yoneda.obj M''))),
            IsSeparated u'.left → Etale u'.left →
            (∀ (B : AlgebraicSpace (Spec (.of k))) (b : B.obj.obj ⟶ yoneda.obj M''),
              (∀ (T : Over (Spec (.of k))) (j : yoneda.obj T ⟶ B.obj.obj),
                AlgebraicSpace.IsEtale j → Flat (yoneda.preimage (j ≫ b)).left) →
              ∀ Y : AlgebraicSpace (Spec (.of k)),
                Function.Bijective (fun g : B.obj.obj ⟶ Y.obj.obj ↦
                  (moduliTwoFiberFst (discreteModuliMap b) f'').comp
                    (discreteModuliMap g))) →
            ∀ η' : f''.comp (discreteModuliMap (yoneda.map u')) ≅ h.comp f,
              (moduliTwoFiberLift f'' h η').toFunctor.IsEquivalence →
              ∃! q : M' ≅ M'', q.hom ≫ u' = u ∧
                Nonempty (ModuliTwoIso
                  (f'.comp (discreteModuliMap (yoneda.map q.hom))) f'') := by
  sorry

/-- Representable separated étale stabilizer-preserving morphisms of algebraic stacks
are closed under composition. All scheme tests, not only geometric points, occur in
the stabilizer hypothesis.
Source: Stacks, Tags 0CIM, 050K and 0DUB
(blueprint: lem-sfb-etale-stabilizer-preserving-affine-moduli).

Proof (step 8 of the node): representability composes by the fibred-groupoid calculus,
étaleness by lem-sfb-stack-chartwise-smooth-etale-calculus and separatedness by
lem-sfb-stack-separation-compactness-permanence. The induced maps on automorphism
sheaves compose. The composite of their bijections on every scheme test is bijective.
-/
theorem etale_stabilizerPreserving_comp
    (k : Type u) [Field k]
    (F : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (G : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (H : BasedCategory.{v₃, w₃} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (hH : IsAlgebraicModuliStack H) (h : BasedFunctor F G) (g : BasedFunctor G H)
    (hr : IsRepresentableByAlgebraicSpaces h) (gr : IsRepresentableByAlgebraicSpaces g)
    (he : IsEtaleModuliMap h) (ge : IsEtaleModuliMap g)
    (hs : ModuliSchemeTest @IsProper (moduliRelativeDiagonal h))
    (gs : ModuliSchemeTest @IsProper (moduliRelativeDiagonal g))
    (ha : ∀ (T : Over (Spec (.of k))) (x : Functor.Fiber F.p T),
      Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap h T).mapIso α))
    (ga : ∀ (T : Over (Spec (.of k))) (x : Functor.Fiber G.p T),
      Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap g T).mapIso α)) :
    IsRepresentableByAlgebraicSpaces (h.comp g) ∧ IsEtaleModuliMap (h.comp g) ∧
      ModuliSchemeTest @IsProper (moduliRelativeDiagonal (h.comp g)) ∧
      ∀ (T : Over (Spec (.of k))) (x : Functor.Fiber F.p T),
        Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap (h.comp g) T).mapIso α) := by
  sorry

/-- The same class of morphisms is stable under base change by any algebraic stack.
The base-change functor is the actual first projection from the specified 2-fibre product.
Source: Stacks, Tags 0CIN, 050F and 0DUB
(blueprint: lem-sfb-etale-stabilizer-preserving-affine-moduli).

Proof (step 8 of the node): use representability, étaleness and separatedness under
arbitrary 2-base change, from the three calculus nodes in the DAG. An object is a
triple (x,b,alpha). An automorphism is a pair (a,c) satisfying
 g(c) alpha = alpha h(a). Given c, the original automorphism-sheaf isomorphism
supplies exactly one a, with h(a) = alpha inverse g(c) alpha. This construction
commutes with all pullbacks and identifies the inertia with the pulled-back inertia.
-/
theorem etale_stabilizerPreserving_baseChange
    (k : Type u) [Field k]
    (F : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (G : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (H : BasedCategory.{v₃, w₃} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (hH : IsAlgebraicModuliStack H) (h : BasedFunctor F G) (g : BasedFunctor H G)
    (hr : IsRepresentableByAlgebraicSpaces h) (he : IsEtaleModuliMap h)
    (hs : ModuliSchemeTest @IsProper (moduliRelativeDiagonal h))
    (ha : ∀ (T : Over (Spec (.of k))) (x : Functor.Fiber F.p T),
      Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap h T).mapIso α)) :
    IsRepresentableByAlgebraicSpaces (moduliTwoFiberFst g h) ∧
      IsEtaleModuliMap (moduliTwoFiberFst g h) ∧
      ModuliSchemeTest @IsProper (moduliRelativeDiagonal (moduliTwoFiberFst g h)) ∧
      ∀ (T : Over (Spec (.of k))) (x : Functor.Fiber (moduliTwoFiberProduct g h).p T),
        Function.Bijective
          (fun α : x ≅ x ↦ (moduliFiberMap (moduliTwoFiberFst g h) T).mapIso α) := by
  sorry

end AlgebraicGeometry
