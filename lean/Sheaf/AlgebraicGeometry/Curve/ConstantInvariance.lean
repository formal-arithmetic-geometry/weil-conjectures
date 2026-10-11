/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
public import Sheaf.AlgebraicGeometry.GenusInvariant

/-!
# Constant coefficients under algebraically closed field extension

Source: Weil conjectures blueprint, sec-curve-estimates/sk-prop-ext-invariance,
thm-sc-constant-invariance (blueprint: thm-sc-constant-invariance).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
thm-sc-constant-invariance (blueprint: thm-sc-constant-invariance).

The witness `r` is constrained to be the canonical cohomology pullback followed by the
constant-sheaf comparison. The witness `t` is the primitive-root trivialization on cohomology.
The equations for the Kummer inclusion, the units boundary, and the Picard boundary express
compatibility with Picard torsion and Picard modulo n. In the proper case the degree-two
identification is constrained by the degree of every line bundle. Compatible bases of Picard
torsion give the degree-one coordinates with the genus of the chosen compactification.
In the affine case the equations are the canonical short exact Kummer ladder, whose Picard
term is the quotient of the compactification's Jacobian described by lem-sc-pic-affine.

Proof following the node:
1. lem-sc-base-change-curve preserves smoothness, separatedness, dimension and properness or
   affineness. lem-weil-separably-closed-geometrically-connected and
   def-pc-geometrically-irreducible give connectedness after base change.
2. Proper case: lem-sc-primitive-root gives compatible trivializations. lem-sc-brauer-zero
   and lem-sc-kummer-les compute degrees one and two, and
   lem-sc-kummer-base-change-compatibility identifies the maps with Picard pullback.
   lem-sc-pic-proper-ntorsion identifies Picard torsion with (Z/n)^(2g).
   thm-sc-jacobian-representability and lem-sc-genus-invariant identify Jacobians after
   base change, and thm-av-final(c) gives bijectivity on their n-torsion points.
   Degree identifies Pic/n with Z/n: lem-pc-rational-points-dense provides a point of degree
   one, whose pullback still has degree one. thm-sc-proper-cohomology gives higher vanishing.
3. Affine case: lem-sc-proper-or-affine reduces to this remaining case.
   thm-sc-affine-cohomology gives H0 = Z/n and vanishing above degree one. In degree one,
   lem-sc-kummer-les and lem-sc-kummer-base-change-compatibility give the canonical ladder.
   Its outer maps are bijective by lem-sc-units-quotient-base-change and the affine clause
   of lem-sc-kummer-base-change-compatibility, using lem-sc-pic-affine and thm-av-final.
   The short five lemma gives bijectivity of the middle map. All equations follow from
   the same Kummer naturality and the compatible primitive roots. -/
theorem IsConnectedCurve.constant_cohomology_baseChange_compatible
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (_hfin : (Set.range c.i.base)ᶜ.Finite)
    (_hclosed : ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z))
    (n : ℕ) [NeZero n] (_hn : (n : k) ≠ 0) :
    ∃ r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q,
      (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q)) ∧
      (∀ q : ℕ, Function.Bijective (r q)) ∧
      ∀ (ζ : k) (hζ : IsPrimitiveRoot ζ n)
        (hζK : IsPrimitiveRoot (algebraMap k K ζ) n),
      ∃ (t : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q ≃+
          Sheaf.H (C.rootsOfUnitySheaf n) q)
        (tK : ∀ q : ℕ,
          Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q ≃+
          Sheaf.H
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).rootsOfUnitySheaf n) q),
        (∀ q : ℕ, (t q).toAddMonoidHom =
          Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom q) ∧
        (∀ q : ℕ, (tK q).toAddMonoidHom = Sheaf.H.map
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
            K)))).constantZModIsoRootsOfUnitySheaf n
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom q) ∧
        (∀ x : Sheaf.H (C.constantZMod n) 1,
          Scheme.Pic.toCohomologicalPicardGroupAddEquiv
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (Additive.ofMul (Scheme.Pic.map
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              ((Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm
                (Sheaf.H.map (kernel.ι (n • 𝟙 C.gmSheaf)) 1 (t 1 x))).toMul)) =
          Sheaf.H.map (kernel.ι (n • 𝟙
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).gmSheaf)) 1
              (tK 1 (r 1 x))) ∧
        (∀ (hnC : IsUnit (n : Γ(C, ⊤)))
          (hnK : IsUnit (n : Γ(pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤))) (L : Additive C.Pic),
          r 2 ((t 2).symm (C.kummerδ₁ n hnC
            (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
          (tK 2).symm
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₁ n hnK
              (Scheme.Pic.toCohomologicalPicardGroupAddEquiv
                (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
                (Additive.ofMul (Scheme.Pic.map
                  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L.toMul))))) ∧
        (IsProper f →
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).genus = c.g.genus ∧
          (∃ (e : Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * c.g.genus) → ZMod n))
            (eK : Sheaf.H
              ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) 1 ≃+
                (Fin (2 * c.g.genus) → ZMod n)),
            ∀ x, eK (r 1 x) = e x) ∧
          ∃ (e : Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n)
            (eK : Sheaf.H
              ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) 2 ≃+
                ZMod n),
            (∀ x, eK (r 2 x) = e x) ∧
            (∀ (hnC : IsUnit (n : Γ(C, ⊤))) (L : Additive C.Pic),
              e ((t 2).symm (C.kummerδ₁ n hnC
                (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
                  (f.picDegree L.toMul : ZMod n)) ∧
            (∀ (hnK : IsUnit (n : Γ(pullback f
                (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤)))
              (L : Additive (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic),
              eK ((tK 2).symm
                ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₁ n hnK
                  (Scheme.Pic.toCohomologicalPicardGroupAddEquiv
                    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L))) =
                  ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).picDegree
                    L.toMul : ZMod n))) ∧
        (∀ [IsProper f],
          ∃ (_ : GeometricallyIntegral f)
            (_ : GeometricallyIntegral
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
            (_ : IsConnectedCurve (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
            (_ : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian f J]
        (e : (picardFunctorDegree f 0).obj.RepresentableBy J), IsPicardZeroMul f e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian (pullback.snd f (Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) JK]
        (eK : (picardFunctorDegree (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          0).obj.RepresentableBy JK), IsPicardZeroMul (pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))) eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ∀ (T : Over (Spec (.of K))) (L : (pullback f (T.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap
        k K))))).Pic)
        (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        T.hom).hom L ∈
          (picardSubfunctorDegree (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op ((Over.map (Spec.map (CommRingCat.ofHom
            (algebraMap k K)))).obj T))
            ⟨L, hL⟩)).left) ∧
        (
          ∃ (_ : GeometricallyIntegral c.g)
            (_ : GeometricallyIntegral
              (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
            (_ : IsConnectedCurve (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))))
            (_ : Smooth (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian c.g J]
        (e : (picardFunctorDegree c.g 0).obj.RepresentableBy J), IsPicardZeroMul c.g e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian (pullback.snd c.g (Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) JK]
        (eK : (picardFunctorDegree (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k
          K))))
          0).obj.RepresentableBy JK), IsPicardZeroMul (pullback.snd c.g (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))) eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ∀ (T : Over (Spec (.of K))) (L : (pullback c.g (T.hom ≫ (Spec.map (CommRingCat.ofHom
        (algebraMap
        k K))))).Pic)
        (hL : L ∈ (picardSubfunctorDegree c.g 0).obj (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso c.g (Spec.map (CommRingCat.ofHom (algebraMap k
        K)))
        T.hom).hom L ∈
          (picardSubfunctorDegree (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso c.g (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree c.g 0).toFunctor).app (.op ((Over.map (Spec.map (CommRingCat.ofHom
            (algebraMap k K)))).obj T))
            ⟨L, hL⟩)).left) ∧
        (IsAffine C → ∀ (hnC : IsUnit (n : Γ(C, ⊤)))
          (hnK : IsUnit (n : Γ(pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤))) (a : Additive Γ(C, ⊤)ˣ),
          r 1 ((t 1).symm (C.kummerδ₀ n hnC a)) =
          (tK 1).symm
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₀ n hnK
              (Additive.ofMul (Units.map
                (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop.hom
                a.toMul)))) ∧
        (IsAffine C → ∀ L : c.Z.Pic, L ∈ c.g.picZero →
          Scheme.Pic.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (Scheme.Pic.map c.i L) =
          Scheme.Pic.map
            (pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K))) c.g (Spec.map
              (CommRingCat.ofHom (algebraMap k K))) c.i (𝟙 _) (𝟙 _)
              ((Category.comp_id f).trans c.comm)
              ((Category.comp_id (Spec.map (CommRingCat.ofHom (algebraMap k K)))).trans
                (Category.id_comp (Spec.map (CommRingCat.ofHom (algebraMap k K)))).symm))
            (Scheme.Pic.map (pullback.fst c.g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L))
              := by
  sorry

end AlgebraicGeometry
