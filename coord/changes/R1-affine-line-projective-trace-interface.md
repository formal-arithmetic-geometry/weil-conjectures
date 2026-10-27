# sfAffineBaseP1TraceAdjunction

## Reason

The assigned affine-line theorem uses arbitrary affine S and the actual standard chart into
ProjectiveSpace (Option (ULift (Fin 1))) S. The sole stated projective input used Spec R and
ULift (Fin 2), and expressed its left adjoint as the proper pushforward rather than the
identity/proper compactification. It also left its stated coefficient-unit normalization
implicit. This made it unusable by direct application in the planned counit calculation.

These are presentations of the same geometric statement: an affine S is canonically Spec
Γ(S, ⊤); both homogeneous coordinate sets have exactly two elements; renaming variables gives
an isomorphism of graded polynomial rings and thus of projective schemes over the base.
Stalkwise invertibility is equivalent to global invertibility by the local criterion for a
unit, with the reverse implication given by germ maps. The identity/proper compactification
represents Rq_* by the derived identity-open-extension comparison, and its projection is the
canonical proper projection. The final scalar equation is the unit specialization already
required by the node, not an extra geometric assumption. The existing geometric theorem
remains unproved and counted as one hole. Its source proof works over any base and is invariant
under coordinate renaming. Empty S, the zero coefficient ring and N=1 cause no exception.

The assigned theorem, its definitions and all target signatures are unchanged. No adopted
WeilConjectures source module is edited. An additional private-import repair below the Tate
pullback theorem breaks the otherwise circular dependency on smooth duality.

## Old

```lean
theorem sfAffineBaseP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (_hN : 0 < N) (hA : (N : A) = 0)
    (R : CommRingCat.{u}) (_hInvertible : IsUnit (N : R)) :
    ∃ (t : ((lowerStar (ModuleCat.{u + 1} A)
          (ProjectiveLine (Spec R) ↘ Spec R)).rightDerivedFunctor).obj
        (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec R)) N A hA))⟦(2 : ℤ)⟧) ⟶
        constantComplex A (Spec R))
      (adj : (lowerStar (ModuleCat.{u + 1} A)
          (ProjectiveLine (Spec R) ↘ Spec R)).rightDerivedFunctor ⊣
        (upperStar (ModuleCat.{u + 1} A)
          (ProjectiveLine (Spec R) ↘ Spec R)).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} A) (ProjectiveLine (Spec R))).obj
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec R)) N A hA))⟦(2 : ℤ)⟧)),
      ∀ K : DerivedCategoryModule A (Spec R),
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
            (ProjectiveLine (Spec R) ↘ Spec R)).app
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec R)) N A hA))⟦(2 : ℤ)⟧)).app K ≫
          adj.counit.app K =
        ((derivedTensor (ModuleCat.{u + 1} A) (Spec R)).map t).app K ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) (Spec R) K).hom
```

## New

```lean
noncomputable abbrev sfProjectiveLineCompactification (S : Scheme.{u}) :
    Compactification (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S) :=
  Compactification.ofIsProper (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)

/-- The canonical identification of a complex with its tensor product with the
pullback of the coefficient unit. Source: the unit normalization in
`thm-amb-p1-adjunction.proof.md`, (G7)
(blueprint: lem-sf-affine-base-p1-trace-adjunction). -/
noncomputable def sfTensorPullbackUnitIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : DerivedCategoryModule A X) :
    B ≅ ((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
      ((L(upperStar (ModuleCat.{u + 1} A) f)).obj (constantComplex A Y)) :=
  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X B).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj B).mapIso
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).symm

/-- The ordinary unbounded projective-line pushforward has the shifted finite Tate
line tensored with inverse image as right adjoint, with the specified actual counit.
We use any affine S and the two coordinates Option (ULift (Fin 1)); these are
the same geometric projective line as the Spec R and ULift (Fin 2) presentation.
The identity/proper compactification realizes Rq_* and its canonical projection.
The unit identification is made explicit by sfTensorPullbackUnitIso.
There is no Noetherian, constructibility, boundedness or Tor-amplitude hypothesis.
The equality for every K includes the coefficient unit: the projection map at that
unit is the canonical unit comparison, so the counit there is t.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md, (G6), (G7), both triangles
(blueprint: lem-sf-affine-base-p1-trace-adjunction).

Proof plan:
1. Apply lem-sp-tower-p1-arbitrary-base-integrals to the arbitrary affine S.
   Reindex its two homogeneous coordinates by Option (ULift (Fin 1)). Its trace t is
   the second projection of the projective-line decomposition. Its base-change
   equations, with lem-asd-etale-finite-twist-pullback, give the two coordinate
   traces on P times_S P. The supported Kummer diagonal class from
   lem-asd-ordinary-supported-kummer has integral one for both projections.
2. Projective-line projections are proper by
   lemma-nagata-projective-space-base-change-proper. The diagonal is closed by
   lem-amb-p1-diagonal-cartier and proper by lem-weil-pbc-closed-immersion-proper.
   Apply lem-kun-0f0g to obtain all unbounded projection isomorphisms. Tensor the
   supported diagonal class with the first pullback of M and push forward along
   the second projection. Inverse projection and inverse proper exchange give a
   natural unit M -> q^*Rq_*M tensor B. Use the normalized monoidal comparisons
   of lem-sfb-ringed-derived-monoidal-comparisons throughout. Define the proposed
   counit by inverse ordered projection, tensoring t with the identity, and the
   unit constraint (def-kun-projection-formula-map).
3. Apply lem-sfb-etale-coordinate-trace-contractions with f = q and d = 1;
   lem-asd-finite-etale-twist-line supplies its line hypothesis. Its first
   coordinate equation, naturality and the section identity of
   lem-sfb-ringed-projection-tensor-composition reduce the first triangle to
   tensoring M with the first diagonal integral, hence to the identity.
4. Its second coordinate equation and the same section identity reduce the
   second triangle to the second diagonal integral. The line self-symmetry is
   identity after etale trivialization, and its shift by two introduces no sign.
   No truncation of either complex is used.
5. The natural maps u |-> G(u) eta and v |-> e F(v) are inverse by the triangles.
   Apply lem-weil-pbc-adjunction-of-natural-bijection. The resulting adjunction
   has the proposed e as its actual counit.
6. Transport the right adjoint through the symmetry from q^*K tensor B to
   B tensor q^*K (lem-kun-tensor-sym). The transported counit is exactly inverse
   proper projection followed by t tensor identity and the left unitor. The
   identity/proper compactification of lem-sf-etale-ambient-adjoint-projection
   gives the same projection map. At the coefficient unit the canonical
   projection and unit constraints identify the counit with t
   (lem-kun-tensor-unit). N = 1 forces A to be the zero ring, where the same
   formulas hold, and the empty affine base causes no exception. -/
theorem sfAffineBaseP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (_hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsAffine S]
    (_hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)) :
    ∃ (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (sfProjectiveLineCompactification S)).obj
        (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧) ⟶
        constantComplex A S)
      (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (sfProjectiveLineCompactification S) ⊣
        (upperStar (ModuleCat.{u + 1} A)
          (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} A)
          (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S)).obj
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine
              (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧)),
      (∀ K : DerivedCategoryModule A S,
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A)
            (sfProjectiveLineCompactification S)).app
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine
              (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧)).app K ≫
          adj.counit.app K =
        ((derivedTensor (ModuleCat.{u + 1} A) S).map t).app K ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) S K).hom) ∧
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (sfProjectiveLineCompactification S)).map
          (sfTensorPullbackUnitIso A
            (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)
            (((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateLine
                (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧)).hom ≫
        adj.counit.app (constantComplex A S) = t
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.SfAffineBaseP1TraceAdjunction
--uses sfAffineBaseP1TraceAdjunction` reported zero downstream modules and only the defining
module itself as a textual user. A full Lean-source search likewise found only its declaration.
No claim for this module or its node was present in coord/claims when the repair was made.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfAffineBaseP1TraceAdjunction | unclaimed | Same projective geometric result, represented in standard-chart coordinates; one existing hole retained. |
| Sheaf.AlgebraicGeometry.SfAffineLineCanonicalDuality | R1 | New private proof import; applies the repaired normalized projective adjunction, compares counits, then restricts along the open chart. Its statement is unchanged. |

## Status

landed 20261024T015854-L-2461580 2026-10-24 (merge of deliver/R1/Sheaf.AlgebraicGeometry.SfAffineLineCanonicalDuality)
