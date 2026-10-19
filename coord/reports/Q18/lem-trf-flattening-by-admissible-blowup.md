## Worker report

The new module `Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup` states
`AlgebraicGeometry.exists_flat_finitePresentation_strictTransform_admissibleBlowup`.
Its only theorem proof is `sorry`. Its docstring gives all ten steps of the node's
proof, following Stacks `flat.tex`, Tag 081R, `lemma-flat-after-blowing-up`, and
`divisors.tex`, Tag 080D, `definition-strict-transform`; both local source passages
were read. No definition, additional theorem, new node, dependency repair, or
statement correction is needed. Only the item's `lean` record changes.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Schemes T and W and a morphism g : W → T | `{T W : Scheme.{u}}` and `(g : W ⟶ T)`, with `universe u` explicitly declared |
| T quasi-compact | `[CompactSpace T]`, the topological quasi-compactness convention for schemes |
| T quasi-separated | `[QuasiSeparatedSpace T]` |
| U an open subscheme of T | `(U : T.Opens)`; its canonical scheme is `U.toScheme`, inclusion `U.ι` |
| U quasi-compact | `(hU : IsCompact (U : Set T))` |
| g of finite type | `[LocallyOfFiniteType g] [QuasiCompact g]`, exactly the conjunction fixed by the dependency record |
| g quasi-separated | `[QuasiSeparated g]` |
| The restriction g⁻¹(U) → U flat | `[Flat (g ∣_ U)]`, using the canonical morphism restriction |
| The same restriction locally of finite presentation | `[LocallyOfFinitePresentation (g ∣_ U)]` |
| There exists a finite type quasi-coherent ideal I | `∃ B : IsAdmissible T U`; `B.I : T.IdealSheafData` is the quasi-coherent ideal and `B.finiteType : B.I.ofFiniteType` |
| I restricts to the unit ideal on U | `B.disjoint_support : Disjoint (U : Set T) (B.I.support : Set T)`; this is exactly the recorded admissible-centre interface, since support here is the zero locus V(I) |
| The blowup T′ = Bl_I(T) and its morphism π | `B.I.blowup` and `B.I.blowupMap`; these are the actual glued blowup and its structure morphism |
| W′ is the scheme-theoretic closure of the open over T minus V(I) inside the fibre product | The domain of `strictTransformMap g B.I.blowupMap B.I.support.compl` is `strictTransform g B.I.blowupMap B.I.support.compl`. Reading its definition shows it is `(strictTransformOpen g B.I.blowupMap B.I.support.compl).ι.image`, the scheme-theoretic image of the indicated open immersion; its closed immersion into the fibre product is `strictTransformι`. In particular the open used here is the full complement of the chosen centre, not just U. |
| W′ → T′ flat | First conjunct `Flat (strictTransformMap g B.I.blowupMap B.I.support.compl)` |
| W′ → T′ of finite presentation | Remaining three conjuncts `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` on this same morphism, exactly as the node specifies |

The existential admissible datum uses its canonical blowup, so the specified
identification in the natural-language admissible-blowup definition is the
identity of `B.I.blowup`. No arbitrary replacement morphism or extra choice is
introduced. Although the recorded admissible definition packages centre data,
that interface supplies exactly the ideal quantified by this item.

Statement dependencies were opened and read, including their complete signatures
and docstrings:

- `def-weil-pbc-scheme-conventions` explicitly introduces no declaration of its own.
  Its conventions are instantiated by the Mathlib classes in the table, with
  finite presentation kept as all three properties.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, whose field says its diagonal is
  quasi-compact; the same file supplies the quasi-separated-space convention.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `AlgebraicGeometry.QuasiCompact` from `Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  the docstring and `Flat.iff_flat_stalkMap` identify its affine definition
  with the node's stalkwise flatness.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, using the mathlib_match
  of `def-sbc-locally-finite-presentation`.
- `WeilConjectures.Blowup.AdmissibleBlowup`:
  `AlgebraicGeometry.IsAdmissible`, its centre `I`, `finiteType`, and
  `disjoint_support`. The real finite-type predicate was also read in
  `WeilConjectures.Compactification.FiniteTypeExtension`.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `blowupMap`.
- `WeilConjectures.Compactification.StrictTransform`:
  `AlgebraicGeometry.strictTransform`, `strictTransformOpen`,
  `strictTransformι`, and `strictTransformMap`. The general recorded construction
  is used at the canonical blowup and the centre's support complement, exactly
  its documented blowup specialization; no duplicate definition is made.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `AlgebraicGeometry.Scheme.Hom.image`, the subscheme of the kernel ideal;
  this is the image construction used by the strict transform.

Statement modules are public imports. Already recorded proof-dependency modules
are ordinary imports: module finite type/presentation, closed immersions,
finite-presentation algebra and base change, the finite-presentation kernel
surjection theorem, quasi-affine immersion into affine space, coherence, and the
strict-transform/blowup comparison. The admissible-blowup module already imports
and provides the product-ideal comparison and isomorphism over the complement.
The current source of the kernel theorem and of the published upstream coherence
module was checked with `scompile.py --source` as well.

Proof-only dependencies without recorded declarations are not imported:
`def-nagata-blowup-flat-base-change-map`, `def-trf-module-strict-transform`,
`lem-trf-flattening-module-by-admissible-blowup`,
`lem-trf-strict-transform-affine-pushforward`,
`lem-trf-strict-transform-composition`, and
`thm-nagata-blowup-flat-base-change`. These do not occur in this statement's type.
Their roles remain in the proof docstring and the unchanged DAG proof.

Edge cases checked against the source and construction:

- U empty: no density assumption appears. The zero centre ideal is admissible
  and its blowup and strict transform are empty, so the conclusion has no
  unwanted nonemptiness condition.
- U all of T: admissibility forces the centre ideal to be the unit ideal; its
  blowup is T. The original morphism is then flat and locally finitely presented,
  and its given quasi-compactness and quasi-separatedness are exactly the other
  two conclusion clauses.
- T or W empty is permitted; neither the binders nor the constructions require
  any point or nonempty affine cover.
- A non-dense U is permitted, and the strict transform still uses T minus V(I).
  It is a scheme-theoretic closure, retaining the correct scheme structure.
- No Noetherian, separated, proper, reduced, characteristic, or field assumption
  is added. `Scheme.{u}` is arbitrary in its explicitly bound universe; all schemes
  in a diagram may be placed in one ambient universe, with no test-scheme
  quantification at a smaller universe.

Searches (all performed before writing the theorem):

- `msearch.py leanfinder`, query “Raynaud Gruson flattening a finite type quasi
  separated scheme by an admissible blowup with flat finitely presented strict
  transform”: 8 hits for `Flat`, universal openness, stalkwise flatness and flat
  descent; no flattening theorem.
- `msearch.py loogle`, query `"strictTransform"`: 0 hits.
- `msearch.py grep`, query `flattening|strictTransform|admissible` in
  `AlgebraicGeometry`: 5 hits, all elliptic-curve admissible variable changes;
  no relevant result.
- `msearch.py leansearch`, query “A finite type quasi separated scheme morphism
  flat and locally finitely presented over a quasi compact open admits an
  admissible blowup with flat finitely presented strict transform”: 8 hits for
  local finite type/presentation, flatness, and quasi-separatedness; no match.
- `rg -n -i 'flattening|flat_after_blow|flat.*admissible|strictTransform.*Flat'`
  in upstream `WeilConjectures` and side `lean/Sheaf`: upstream comments in
  `Blowup.AdmissibleBlowup` and `Compactification.EliminationOfIndeterminacy`
  explicitly explain that their formalized route omits module flattening and
  Tags 0815/081R. Other hits in the side library concern unrelated notions.
- `grep -rn 'lem-trf-flattening-by-admissible-blowup'` in upstream sources:
  no hit. An exact-name `rg` for the new declaration in Mathlib, upstream,
  side `lean/Sheaf`, and `dag/lean_names_upstream.json` likewise had no hit.

No statement dispute or node fault was found. The existing constructions render
the statement without adding any missing notion.

Validation: `scompile.py Q18 lem-trf-flattening-by-admissible-blowup` compiled the
single delivered file both as a sandbox and as its library module, with exit 0
and no warnings or errors (reported times 4.3 s and 3.4 s). The file has no line
over 100 characters. All universes and variables are bound explicitly.

## Second reading by Q18

The group delivered no independent second reading: the previous text of this section said
none was performed. This reading was done by the maintainer reviewer
(cc review service, run 2) in its place. The node, the source passages (Stacks `flat.tex`
Tag 081R `lemma-flat-after-blowing-up`; `divisors.tex` Tag 080D
`definition-strict-transform`), every statement dependency record and the Lean file were
open while it was done. The module and the node record are unchanged; only this section is
replaced.

| Node clause | Lean | Verdict |
| --- | --- | --- |
| scheme T | `{T : Scheme.{u}}` | same |
| T quasi-compact | `[CompactSpace T]` | same, def-weil-pbc-scheme-conventions |
| T quasi-separated | `[QuasiSeparatedSpace T]` | same |
| U ⊆ T quasi-compact open | `(U : T.Opens) (hU : IsCompact (U : Set T))` | same; with T quasi-separated this makes `U.ι` quasi-compact, as `def-nagata-admissible-blowup` requires |
| g : W → T | `{W : Scheme.{u}} (g : W ⟶ T)` | same; a morphism forces one universe |
| g of finite type | `[LocallyOfFiniteType g] [QuasiCompact g]` | same, the pair in the record of def-weil-finite-type-morphism |
| g quasi-separated | `[QuasiSeparated g]` | same |
| g⁻¹(U) → U flat | `[Flat (g ∣_ U)]` | same: `morphismRestrict` is the map g⁻¹ᵁU ⟶ U |
| g⁻¹(U) → U locally of finite presentation | `[LocallyOfFinitePresentation (g ∣_ U)]` | same |
| ∃ finite type quasi-coherent ideal I with I restricted to U equal to O_U | `∃ B : IsAdmissible T U` (`B.I : T.IdealSheafData`, quasi-coherent by construction; `B.finiteType : B.I.ofFiniteType`, finitely generated on every affine open; `B.disjoint_support`) | same: the support of an `IdealSheafData` is V(I), so disjointness from U is I restricted to U being the unit ideal; this is the recorded declaration of def-nagata-admissible-blowup |
| π : Bl_I(T) → T | `B.I.blowupMap : B.I.blowup ⟶ T` | same, recorded declaration of def-nagata-global-blowup |
| W′ = scheme-theoretic closure in W ×_T T′ of the open over T ∖ V(I) | domain of `strictTransformMap g B.I.blowupMap B.I.support.compl` = `(strictTransformOpen g π V(I)ᶜ).ι.image`, with `strictTransformOpen = pullback.snd ⁻¹ᵁ (π ⁻¹ᵁ V(I)ᶜ)` | same: `Scheme.Hom.image` is the recorded scheme-theoretic image; it is by definition `Scheme.IdealSheafData.strictTransform B.I g` (StrictTransform.lean:428), the recorded declaration of def-nagata-strict-transform; the open is the full complement of V(I), not U |
| W′ → T′ flat | `Flat (strictTransformMap …)` | same; `strictTransformMap = strictTransformι ≫ pullback.snd` is the map to T′ |
| W′ → T′ of finite presentation, that is LFP, QC and QS | the three remaining conjuncts | same, all three present |

Quantifier order is the same: hypotheses, then ∃ centre, then the four properties of
the strict transform of that centre. Nothing stronger is assumed: no Noetherian,
separated, reduced, density or field hypothesis. Nothing is weaker: no clause is dropped.

Edge cases. If U = ∅, the zero ideal is admissible; its blowup and the strict transform are empty,
which agrees with 081R (no density of U is assumed there). If U = T, disjointness forces
`B.I.support = ⊥`, the unit ideal, and the blowup is T itself. If T or W is empty, no
binder needs a point. Universes: one explicit `u`; no auto-bound variable.

One definition per notion: the general `AlgebraicGeometry.strictTransform` at the blowup
and V(I)ᶜ is definitionally the blowup specialization `Scheme.IdealSheafData.strictTransform`,
so no second strict transform is introduced. `rg -i "flat.*strictTransform|flatten"` on
upstream `WeilConjectures` and side `lean/Sheaf` finds no flattening theorem; the upstream
comments in `Blowup/AdmissibleBlowup.lean` state that module flattening (0815/081R) is
outside its formalized route.

Docstrings and imports. The module docstring names Tag 081R and 080D with
`(blueprint: lem-trf-flattening-by-admissible-blowup)`. The theorem docstring carries all
ten proof steps of the node. The proof is `sorry`. Public imports are the statement's
modules. The private imports are the stated proof dependencies' modules
(ClosedImmersion, ModuleCat.Sheaf.Generators, RingTheory.FinitePresentation/FiniteStability,
the kernel-surjection module, AffineSpace, Coherent, StrictTransformBlowup).

Compile: `tools/nt_compile.py --json` on the delivered file gives exit 0 and no message,
6.3 s. No line is over 100 characters.

Mismatches found: none in the Lean or the node record. The only fault was this section.
