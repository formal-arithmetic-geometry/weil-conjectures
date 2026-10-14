## What changed

Repaired `standardSingleFlatCounit_localization_homology` by replacing the false arbitrary
bounded-flat complex quantifier with the complex constructed from `K := Classical.choose hpres`.
The construction takes the stalk of the restricted presentation complex at `⟨g a, hS⟩`
and transports scalars along `S.stalkIso`; the theorem exposes an equality identifying its
returned `P'` with that constructed stalk complex. Adapted the completion caller to obtain
its `P`, bounds, flatness, and derived data from the repaired theorem.

## Proved and sorry left

The theorem `standardSingleFlatCounit_localization_homology` remains a named `sorry`; its
statement is repaired as requested. No additional holes were added. The adapted completion
caller has a complete proof.

## No longer needed

The completion proof no longer uses `standardSingleFlatCounit_localization_data` or
`standardSingleFlatCounit_localization_pair`. Their plain imports were removed because the repaired homology theorem now supplies the complex, its bound, flatness and derived pair.

## Where the brief, the DAG or earlier work was wrong

The returned interface quantified over an arbitrary `P`, unrelated to the presentation witness
in `hpres`, making the statement false. The node and caller now carry the actual stalk complex
from that witness.

## New nodes

None.

## Forced adaptations

`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion` was adapted because
its old caller passed an independently chosen `P`; it now destructures the repaired theorem's
constructed `P` and uses the returned bounds and flatness. No existing signatures were changed.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository versions. Existing declaration signatures
are unchanged except for the declared repair of `standardSingleFlatCounit_localization_homology`;
the completion adaptation is proof and import only. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; there are no compiler errors, forbidden
constructs, or new unnamed sorries. The homology theorem remains the named split-off sorry.
Verdict: pass.
3. The repaired interface constructs the complex from `Classical.choose hpres`; its bounds,
flatness, and equality are explicit and no arbitrary witness is chosen. The split node and
change record document the altered statement. Verdict: pass.
4. The proof follows the presentation witness and the completion caller uses it. The unused
localization data and pair imports were removed from the adapted completion module. Verdict: pass.
5. The node statement, Lean declaration, proof origin, and forced adaptation agree; the unit
route remains through the homology node and completion caller. Verdict: pass.

Changed the completion imports and formatting, added the interface change record `coord/changes/standardSingleFlatCounit_localization_homology.md`, and added
this review section.

## Forced adaptations

### Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-20dhyrz8/lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationCompletion.lean:90:41: error: Function expected at
  standardSingleFlatCounit_localization_homology (fun {Y₀ B₀ A₀} ↦ h_affine) p M hM g a S V hS hV hSaff hVaff hVS hpres
but this term has type
  let R := B.presheaf.stalk (g a);
  let T := A.presheaf.stalk a;
  have K := Classical.choose hpres;
  let xS := ⟨g a, hS⟩;
  have P :=
    ((ModuleCat.restrictScalars (CommRingCat.Hom.hom (S.stalkIso xS).inv)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
      ((((↑S).toRingedSpace.moduleStalkFunctor xS).mapHomologicalComplex (ComplexShape.up ℤ)).obj K);
  ∃ P',
    P' = P ∧
      (∃ b, ∀ (i : ℤ), b < i → IsZero (P'.X i)) ∧
        (∀ (i : ℤ), Module.Flat ↑R ↑(P'.X i)) ∧
          ∃ LF ε,
            ∃ (_ : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat ↑R) (ComplexShape.up ℤ))),
              ∀ (n : ℤ),
                ∃ eL eR,
                  (A.toRingedSpace.moduleStalkFunctor a).map
                      ((DerivedCategory.homologyFunctor A.toRingedSpace.Modules n).map
                        (standardSingleBaseChangeMap p M g)) =
                    eL.hom ≫
                      (DerivedCategory.homologyFunctor (ModuleCat ↑(A.toRingedSpace.presheaf.stalk a)) n).map
                          (ε.app ((HomotopyCategory.quotient (ModuleCat ↑R) (ComplexShape.up ℤ)).obj P')) ≫
                        eR.hom

Note: Expected a function because this term is being applied to the argument
  P

(with the modules compiled into /tmp/forced-adaptation-20dhyrz8/.lbuild) [6.7 s]
```
The adapted module compiles. The old independent data and pair obtains and the application to P, hPbound, hPflat, LF, ε and hLF must be replaced because homology now returns those witnesses existentially. The new obtain also unpacks P′ = P; the final tuple discards that equality to preserve the completion signature. The two removed imports supplied only the obsolete obtains.

## Second reading by A3

1. Interfaces: I compared the delivered homology module and forced completion adaptation with the repository versions. The homology theorem intentionally has the recorded interface repair: it constructs `P` from `Classical.choose hpres` and returns `P' = P`; the completion theorem's public signature is unchanged and its proof-only adaptation is forced by that repair. Verdict: pass.
2. Proofs and axioms: both sandbox modules compile with `lcompile.py --all`. The only remaining `sorry` is the named homology theorem, which is listed above and has the matching split node. No forbidden declaration or `sorry` inside a definition was introduced. Verdict: pass.
3. New or changed statement: the old arbitrary-`P` interface is false, and the repaired statement ties the returned complex to the localized presentation witness. The equality `P' = P`, bound, flatness, derived pair, and homology compatibility are explicit and match the node and change record. Verdict: pass.
4. Route and pruning: the completion proof now uses the homology theorem as the sole source of its complex, bounds, flatness, and derived pair; the obsolete localization-data and localization-pair imports are removed. The unit route still passes through the homology and completion nodes. Verdict: pass.
5. DAG and records: the node's Lean statement, split status, source, proof origin, and recorded statement change agree with the delivered declaration; the forced adaptation and its compiler error are documented. No imports or proof dependencies were removed beyond those recorded. Verdict: pass.

I changed only this report by adding this second-reading record.

## Forced adaptations

### Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-5oaq7zps/lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationCompletion.lean:90:41: error: Function expected at
  standardSingleFlatCounit_localization_homology (fun {Y₀ B₀ A₀} ↦ h_affine) p M hM g a S V hS hV hSaff hVaff hVS hpres
but this term has type
  let R := B.presheaf.stalk (g a);
  let T := A.presheaf.stalk a;
  have K := Classical.choose hpres;
  let xS := ⟨g a, hS⟩;
  have P :=
    ((ModuleCat.restrictScalars (CommRingCat.Hom.hom (S.stalkIso xS).inv)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
      ((((↑S).toRingedSpace.moduleStalkFunctor xS).mapHomologicalComplex (ComplexShape.up ℤ)).obj K);
  ∃ P',
    P' = P ∧
      (∃ b, ∀ (i : ℤ), b < i → IsZero (P'.X i)) ∧
        (∀ (i : ℤ), Module.Flat ↑R ↑(P'.X i)) ∧
          ∃ LF ε,
            ∃ (_ : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat ↑R) (ComplexShape.up ℤ))),
              ∀ (n : ℤ),
                ∃ eL eR,
                  (A.toRingedSpace.moduleStalkFunctor a).map
                      ((DerivedCategory.homologyFunctor A.toRingedSpace.Modules n).map
                        (standardSingleBaseChangeMap p M g)) =
                    eL.hom ≫
                      (DerivedCategory.homologyFunctor (ModuleCat ↑(A.toRingedSpace.presheaf.stalk a)) n).map
                          (ε.app ((HomotopyCategory.quotient (ModuleCat ↑R) (ComplexShape.up ℤ)).obj P')) ≫
                        eR.hom

Note: Expected a function because this term is being applied to the argument
  P

(with the modules compiled into /tmp/forced-adaptation-5oaq7zps/.lbuild) [7.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
