# integralStratifiedPerfectClosure_truncation

## Reason

The parent already states the equivalence with bounded constructible cohomology before
its closure theorem. Prove truncation closure directly there, as its original docstring
specifies, and withdraw the redundant split. Triangulated closure alone, the split's
sole dependency, does not imply truncation closure. The existing characterization proof
remains a pre-existing separate obligation and is not duplicated or moved.

The now-landed N3 homology proof imports this split and calls it twice. Preserve that
proof, signature and public imports, migrating only its private import and two calls
to the parent's truncation clause. The parent must then drop its homology import and
prove that clause directly, to avoid a cycle. Its complete proof uses the same bounded
cohomology characterization: H^q(K)[0] has the permitted sheaf in degree zero and zeros
elsewhere. No public declaration is added to either adapted module.

## Old

The withdrawn standalone theorem signature:

```lean
theorem integralStratifiedPerfectClosure_truncation
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K) (n : ℤ) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.TStructure.t.truncGE n).obj K)
```

The old parent branches:

```lean
  · intro K hK n
    exact integralStratifiedPerfectClosure_truncation T l E _hdim _hl K hK n
  · intro K hK q
    exact integralStratifiedPerfectClosure_homology T l E _hdim _hl K hK q

```

The homology module privately imported IntegralStratifiedPerfectClosureTruncation and
its two calls were:

```lean
  have hL : P L :=
    (integralStratifiedPerfectClosure_truncation T l E _hdim _hl K hK q).1
  have hM : P M :=
    (integralStratifiedPerfectClosure_truncation T l E _hdim _hl L hL q).2
```

## New

The item is withdrawn via deleted.txt and lands as an empty module. Its node is retained
with lean null. The parent removes both closure proof imports, privately imports
HomologyProperty, and replaces its last two branches with:

```lean
  · let Q : ObjectProperty (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
      IsIntegralStratifiedFinitelyPresented T (pbcIntegralDatum l E)
    have : Q.IsClosedUnderIsomorphisms := ⟨by
      rintro F G e ⟨s, hs⟩
      refine ⟨s, fun i ↦ ?_⟩
      obtain ⟨V, hV, hlocal⟩ := hs i
      refine ⟨V, hV, fun U f hf ↦ ?_⟩
      obtain ⟨N, hN, ⟨eN⟩⟩ := hlocal U f hf
      exact ⟨N, hN, ⟨((SheafOfModules.overFunctor _ U).mapIso
        ((proEtaleModuleInverseImage (s.immersion i)
          (pbcAdicCompletion T (pbcIntegralDatum l E))).mapIso e)).symm ≪≫ eN⟩⟩⟩
    have criterion (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
        PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
          IsIntegralBoundedConstructibleCohomology T (pbcIntegralDatum l E) K := by
      have hchar := integralStratifiedPerfectCharacterization T l E _hdim _hl K
      exact hchar.1.trans hchar.2
    constructor
    · intro K hK n
      obtain ⟨⟨a, b, hab, ha, hb⟩, hcoh⟩ := (criterion K).mp hK
      have : Q.ContainsZero := ⟨_, DerivedCategory.isZero_of_isLE K b (b + 1) (by omega),
        hcoh (b + 1)⟩
      have hQ : DerivedCategory.homologyProperty Q K := hcoh
      constructor
      · apply (criterion _).mpr
        exact ⟨⟨a, b, hab, inferInstance, inferInstance⟩,
          DerivedCategory.homologyProperty_truncLE hQ n⟩
      · apply (criterion _).mpr
        exact ⟨⟨a, b, hab, inferInstance, inferInstance⟩,
          DerivedCategory.homologyProperty_truncGE hQ n⟩
    · intro K hK q
      obtain ⟨⟨a, b, _, ha, hb⟩, hcoh⟩ := (criterion K).mp hK
      have : Q.ContainsZero := ⟨_, DerivedCategory.isZero_of_isLE K b (b + 1) (by omega),
        hcoh (b + 1)⟩
      apply (criterion _).mpr
      refine ⟨⟨0, 0, le_rfl, inferInstance, inferInstance⟩, fun r ↦ ?_⟩
      change Q _
      by_cases hr : r = 0
      · subst r
        exact Q.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          ((DerivedCategory.homologyFunctor _ q).obj K)).symm (hcoh q)
      · apply Q.prop_of_isZero
        rcases lt_or_gt_of_ne hr with hr | hr
        · exact DerivedCategory.isZero_of_isGE _ 0 r hr
        · exact DerivedCategory.isZero_of_isLE _ 0 r hr

```

The outer conjunction has three branches so the final pair shares Q's isomorphism
invariance. The parent signature is unchanged. The homology module replaces only its
private truncation import with IntegralStratifiedPerfectCharacterization and its two calls
with:

```lean
  have hL : P L :=
    ((integralStratifiedPerfectClosure T l E _hdim _hl).2.2.1 K hK q).1
  have hM : P M :=
    ((integralStratifiedPerfectClosure T l E _hdim _hl).2.2.1 L hL q).2
```

Its entire remaining proof, statement, docstring, attributes and public imports are
unchanged. Both adapted modules compile as a set. No holes are introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralStratifiedPerfectClosureTruncation | N4 | Withdraw redundant split. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | K2 | Forced adaptation: replace two proof branches and their private imports; existing signatures and public interface identical. |
| Sheaf.Paper.IntegralStratifiedPerfectClosureHomology | currently unclaimed; N3's new proof landed during this session | Preserve signature and proof structure; migrate one import and two calls. |

Initially the only consumer was the characterization module. The N3 landing added the
homology module as a second consumer; both are adapted against the current source in
this packet. Searches of lean/, quarantine/, DAG nodes and units show no other parent
and no unit realization. The characterization node removes both split dependencies;
the homology node migrates its truncation dependency to the characterization node.
The withdrawn item's node refers to the actual replacement in the characterization
module. No DAG node is deleted and no target statement or definition changes.

Return repair (head 5052ddcc9): the adapted module
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization` is held by K2. The earlier
description as currently unclaimed was stale. This record now names its holder K2
explicitly; the forced adaptation remains confined to the proof and private imports
described above.

## Status

landed 20261021T014718-L-2447196 2026-10-21 (merge of deliver/N4/Sheaf.Paper.IntegralStratifiedPerfectClosureTruncation)
