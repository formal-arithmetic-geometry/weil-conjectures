# AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability

## Reason

The assigned theorem podGeneralCtfAdjunctions needs the first clause of the
already stated proof dependency det-thm-sf-ctf-stability-internal-hom. Its Lean
module was removed on 2026-10-20 as unused, according to the node's lean.note.
The current PodCtfAdjunctions node still names it as a proof dependency, and its
unfinished proof needs it. Restore the existing full statement and its explicit
auxiliary definitions under its original module and declaration names.

## Old

lean/Sheaf/Paper/DetThmSfCtfStabilityInternalHom.lean is absent. The node retains
its Lean attachment and complete statement, auxiliary declaration inventory,
twelve proof steps, and proof dependencies. The existing attachment is
AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability.

The preserved old Lean record gives the signature verbatim:

```lean
theorem internalHom_stability (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (K L : moduleDerived Λ X) (_hK : dctfPred Λ X K) (_hL : dctfPred Λ X L) : dctfPred Λ X (internalHomObj Λ X K L) ∧ (∀ (S Sbar : Scheme.{u}) (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X), (hu : IsOpenImmersion u) → (hi : IsClosedImmersion i) → a = u ≫ i → ∀ (P : moduleDerived Λ S), IsLocallyConstantPerfectComplex Λ S P → ∃ (h : ∀ N, localizingClosureProEtale Λ S N → localizingClosureProEtale Λ X ((locallyClosedExtension Λ u i hu hi).obj N)) (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤ (localizingClosureProEtale Λ S).FullSubcategory), Nonempty (localizingLocallyClosedExtension Λ u i hu hi h ⊣ G) ∧ ∃ N : (localizingClosureProEtale Λ X).FullSubcategory, N.obj = L ∧ Nonempty (internalHomObj Λ X ((locallyClosedExtension Λ u i hu hi).obj P) L ≅ (CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj (internalHomObj Λ S P (G.obj N).obj)) ∧ Nonempty ((CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj (internalHomObj Λ S P (G.obj N).obj) ≅ (CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj (dualTensorObj Λ S P (G.obj N).obj))) ∧ ∀ K' : moduleDerived Λ X, dctfPred Λ X K' → ∀ Q : ObjectProperty (moduleDerived Λ X), Q.IsTriangulated → Q.IsClosedUnderIsomorphisms → (∀ J : moduleDerived Λ X, internalHomGenerator Λ X J → Q J) → Q K'
```

## New

Restore the module with that full statement, not merely the membership projection.
The theorem remains `:= by sorry`, with all twelve recorded proof steps in its
docstring and the original blueprint identifier. Its conclusion includes finite-Tor
membership, both locally closed internal-Hom formulas, and generation by finite
shifts and cones. The binder for the open immersion is named j instead of u to
avoid confusing it with the universe; this has no mathematical effect.

The auxiliary declarations are direct constructions: moduleDerived is the
ambient derived category; dctfPred is the intersection of constant-model bounded
constructibility with finite Tor amplitude; internalHomObj evaluates derivedHom;
dualTensorObj tensors relativeInternalHomDual with its second argument;
locallyClosedExtension is derived openImmersionLowerShriek followed by derived
lowerStar; localizingLocallyClosedExtension is ObjectProperty.lift of that same
functor; internalHomGenerator is the isomorphism closure of the displayed
locally closed scalar-perfect objects. No data is chosen from a theorem.

The exact restored theorem signature is recorded verbatim in the delivered copy
of dag/nodes/sec-six-functors-basics/det-thm-sf-ctf-stability-internal-hom.json,
field lean.statement, and in the restored Lean module.

The restored signature is:

```lean
theorem internalHom_stability
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (K L : moduleDerived Λ X) (_hK : dctfPred Λ X K) (_hL : dctfPred Λ X L) :
    dctfPred Λ X (internalHomObj Λ X K L) ∧
    (∀ (S Sbar : Scheme.{u}) (a : S ⟶ X) (j : S ⟶ Sbar) (i : Sbar ⟶ X),
      (hj : IsOpenImmersion j) → (hi : IsClosedImmersion i) → a = j ≫ i →
      ∀ (P : moduleDerived Λ S), IsLocallyConstantPerfectComplex Λ S P →
      ∃ (h : ∀ N, localizingClosureProEtale Λ S N → localizingClosureProEtale Λ X
          ((locallyClosedExtension Λ j i hj hi).obj N))
        (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
          (localizingClosureProEtale Λ S).FullSubcategory),
        Nonempty (localizingLocallyClosedExtension Λ j i hj hi h ⊣ G) ∧
        ∃ N : (localizingClosureProEtale Λ X).FullSubcategory, N.obj = L ∧
          Nonempty (internalHomObj Λ X ((locallyClosedExtension Λ j i hj hi).obj P) L ≅
            (CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj
              (internalHomObj Λ S P (G.obj N).obj)) ∧
          Nonempty ((CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj
              (internalHomObj Λ S P (G.obj N).obj) ≅
            (CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj
              (dualTensorObj Λ S P (G.obj N).obj))) ∧
    ∀ K' : moduleDerived Λ X, dctfPred Λ X K' →
      ∀ Q : ObjectProperty (moduleDerived Λ X), Q.IsTriangulated →
        Q.IsClosedUnderIsomorphisms →
        (∀ J : moduleDerived Λ X, internalHomGenerator Λ X J → Q J) → Q K'
```

## Users

`tools/downstream.py Sheaf.Paper.DetThmSfCtfStabilityInternalHom --uses
internalHom_stability` reports `unknown module(s)` because the module is absent
from the base source tree. A direct rg over lean/Sheaf and lean/WeilConjectures
finds no current use of internalHom_stability or import of the absent module.
The existing DAG parent is det-thm-sf-ctf-stability-adjunctions. Its assigned Lean
module is the new direct consumer in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | absent, restored here | Existing node and full statement restored; one named proof hole. |
| Sheaf.Paper.PodCtfAdjunctions | H1, assigned item | Private proof import; uses only the membership projection. Existing signatures and definitions unchanged. |

No existing target definition or statement changes. No consumer adaptation is
needed, since the restored module has no current source importers. The restored
node's attachment and proof dependencies are preserved.

## Status

landed 20261025T163640-L-747654 2026-10-25 (merge of deliver/H1/Sheaf.Paper.PodCtfAdjunctions)
