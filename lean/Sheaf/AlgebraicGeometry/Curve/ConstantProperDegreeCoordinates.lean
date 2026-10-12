/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

/-!
# Degree-normalized proper cohomology coordinates

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
proof of thm-sc-constant-invariance, proper case in degree two
(blueprint: lem-sc-constant-proper-degree-coordinates).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
proof of thm-sc-constant-invariance, proper case in degree two
(blueprint: lem-sc-constant-proper-degree-coordinates).

Proof: a proper curve's open immersion into its smooth connected proper compactification is
proper, so its image is closed as well as open and nonempty; connectedness makes the image
all of the compactification. The immersion is an isomorphism over k and preserves genus.
Over both fields the Kummer sequence, Brauer vanishing and divisibility of Picard degree
zero identify H2(mu_n) with Pic/n and then with ZMod n by degree. Surjectivity of degree
follows from a rational point of degree one. Compose these degree identifications with the
specified primitive-root trivializations to obtain e and eK. They satisfy the displayed
boundary equations by construction. Kummer naturality and preservation of line-bundle
degree under extension give eK(r x) = e x; the Kummer boundary is surjective, so checking
this equality on its image checks every class. These maps are equivalences also for n = 1,
when both groups are zero. -/
theorem IsConnectedCurve.constant_proper_degree_coordinates
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (_hfin : (Set.range c.i.base)ᶜ.Finite)
    (_hclosed : ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z))
    (n : ℕ) [NeZero n] (_hn : (n : k) ≠ 0)
    (r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q)
    (hr : (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q)))
    (ζ : k) (hζ : IsPrimitiveRoot ζ n)
    (hζK : IsPrimitiveRoot (algebraMap k K ζ) n)
    (t : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q ≃+
          Sheaf.H (C.rootsOfUnitySheaf n) q)
        (tK : ∀ q : ℕ,
          Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q ≃+
          Sheaf.H
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).rootsOfUnitySheaf n) q)
    (ht : (∀ q : ℕ, (t q).toAddMonoidHom =
          Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom q))
    (htK : (∀ q : ℕ, (tK q).toAddMonoidHom = Sheaf.H.map
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
            K)))).constantZModIsoRootsOfUnitySheaf n
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom q))
    [IsProper f] :
    f.genus = c.g.genus ∧
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
                    L.toMul : ZMod n)) := by sorry

end AlgebraicGeometry
