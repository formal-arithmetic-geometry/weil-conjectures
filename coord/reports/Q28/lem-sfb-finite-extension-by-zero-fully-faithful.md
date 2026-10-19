## Worker report

The node is already stated exactly by the sorry-free upstream declaration
`AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek`; therefore this
 delivery adds no Lean module.  The node copy records it as an existing declaration:

- module: `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful`;
- declaration: `AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek`;
- source signature (verbatim, through the declaration header):
  `noncomputable def ProEtale.fullyFaithfulOpenImmersionLowerShriek :\n`
  `    (j)_!open[A].FullyFaithful`.

The source file binds `A : Type u'` with
`[Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]`, and
`{U X : Scheme.{u}}`, `j : U ⟶ X`, and `[IsOpenImmersion j]`.  Thus the node's
“open immersion” hypothesis is rendered by `j` and `[IsOpenImmersion j]`, while its
coefficient context is the Grothendieck abelian category used by the referenced
extension-by-zero definition.  The conclusion “the extension by zero `j_!` is fully
faithful” is rendered by `(j)_!open[A].FullyFaithful`.  The preceding upstream instance
`ProEtale.isIso_openImmersionLowerShriekAdjunction_unit` supplies the invertible unit,
and the declaration is the fully-faithful functor obtained from that unit; the adjacent
`full_openImmersionLowerShriek` and `faithful_openImmersionLowerShriek` instances expose
the two components of full faithfulness.

The statement dependency `def-sfb-finite-extension-by-zero` is the existing declaration
`AlgebraicGeometry.ProEtale.openImmersionLowerShriek` in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`, lines 294--298.
Its signature is the canonical functor
`Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A` for the same
`A`, `U`, `X`, `j`, and open-immersion instance.  The proof dependencies named by the
node were also read in their recorded source modules: the extension-by-zero adjunction
is `AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction` (and its
restriction computation `openImmersionRestriction_obj_val_obj`) in that same
`LowerShriek.OpenImmersion.Defs` module; the lower-star notion is
`AlgebraicGeometry.ProEtale.lowerStar` and its objectwise computation
`lowerStar_obj_val_obj` in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.

Edge cases checked against the quantified source context: the identity open immersion
`j = 𝟙 X` is included; the empty open scheme is allowed and gives the fully faithful
functor from its (possibly zero) sheaf category; no clopen, proper, separated, or
nonempty-range hypothesis is present; arbitrary coefficient universes `u'` and scheme
universe `u` are retained.  The declaration uses no `sorry`.

Searches for an existing notion or statement:

- `msearch.py ... leanfinder "extension by zero fully faithful open immersion pro-etale sheaves"`:
  eight unrelated fully-faithful hits, with no pro-etale extension-by-zero match.
- `msearch.py ... leanfinder "AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek"`:
  eight unrelated Mathlib hits, with no exact match (the exact source declaration was
  then verified by direct source grep).
- `msearch.py ... loogle "FullyFaithful openImmersionLowerShriek"`: zero hits;
  Loogle reported `FullyFaithful` as unknown in that query.
- `msearch.py ... grep "fullyFaithfulOpenImmersionLowerShriek" "Mathlib"`:
  zero hits.
- `msearch.py ... grep
  "fullyFaithfulOpenImmersionLowerShriek|openImmersionLowerShriek"
  "/home/ubuntu/weil-newtargets-shared/lean/Sheaf": no declaration of the exact
  fully-faithful name; the 25 hits are downstream uses of
  no declaration of the exact fully-faithful name; the 25 hits are downstream uses of
  other `openImmersionLowerShriek` declarations.
- Direct `rg` in the pinned `WeilConjectures/` source found the exact declaration and its
  docstring at `SixFunctors/ProEtale/LowerShriek/OpenImmersion/FullyFaithful.lean`,
  lines 85--88; the surrounding variables and open-immersion context are at lines
  69--70.  This is an exact statement match, so no duplicate module is written.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q28

I reread the node copy at `dag/nodes/sec-six-functors-basics/lem-sfb-finite-extension-by-zero-fully-faithful.json`, its blueprint source place, and the recorded dependency nodes before checking the upstream declaration.

The node statement has the following list of ingredients and clauses, each of which is rendered by the existing declaration:

1. The object `j : U ⟶ X` is an open immersion.  The declaration binds
   `{U X : Scheme.{u}}`, `(j : U ⟶ X)`, and `[IsOpenImmersion j]`.
2. The coefficient category is a Grothendieck abelian category.  The declaration binds
   `A : Type u'` with `[Category.{u + 1} A]`, `[Abelian A]`, and
   `[IsGrothendieckAbelian.{u + 1} A]`; this is the coefficient context used by the
   recorded `def-sfb-finite-extension-by-zero` declaration.
3. The extension-by-zero object is the canonical functor from that dependency, rendered
   by the scoped notation `(j)_!open[A]` for
   `AlgebraicGeometry.ProEtale.openImmersionLowerShriek A j`.
4. The conclusion that this functor is fully faithful is exactly the result type
   `(j)_!open[A].FullyFaithful` of
   `AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek`.

The quantifier order and universes agree: `A` and its instances precede the scheme
variables, and both schemes use the shared universe `u` while the coefficient type uses
`u'`.  No extra separation, properness, clopen-range, nonemptiness, characteristic, or
finite-type hypothesis appears.  The declaration is a noncomputable definition of the
`FullyFaithful` structure, so it states the node's full conclusion rather than only its
`Full` or `Faithful` projections.  The adjacent `full_...` and `faithful_...` instances
are consequences and do not alter the item's statement.

I checked the source proof context: the unit of
`ProEtale.openImmersionLowerShriekAdjunction A j` is made invertible by the adjoint-triple
criterion and the already recorded invertible counit for
`ProEtale.openImmersionRestrictionLowerStarAdjunction`; the declaration then applies
`fullyFaithfulLOfIsIsoUnit`.  This uses the canonical extension-by-zero functor from the
dependency, not a private copy.

Edge cases remain covered by the binders: `j = 𝟙 X`, an empty open scheme, a zero sheaf or
zero coefficient object, and all allowed coefficient and scheme universes are included.
No index set, integer parameter, characteristic, or nonempty-range condition is present.

For H4 searches I checked LeanFinder and Loogle queries recorded in `searches.jsonl`,
grepped Mathlib and `lean/Sheaf`, and directly searched the pinned
`WeilConjectures/` source and `dag/lean_names_upstream.json`.  Mathlib and `lean/Sheaf`
contain no competing declaration; the pinned source contains the exact declaration at
`WeilConjectures/SixFunctors/ProEtale/LowerShriek/OpenImmersion/FullyFaithful.lean`,
lines 85--88.  The dependency declarations were also opened: the canonical
`openImmersionLowerShriek` is in `LowerShriek/OpenImmersion/Defs`, and the adjunction and
lower-star declarations used by the source proof have the same `A`, `U`, `X`, `j`, and
`[IsOpenImmersion j]` context.

No mismatch was found, so no Lean module or node field was changed.  In particular, the
existing upstream declaration is not replaced by a duplicate statement, and no proof or
definition data is introduced in this delivery.

Additional independent searches: LeanSearch `extension by zero is fully faithful`
returned eight unrelated results (chiefly extension of homological complexes), and
LeanFinder `a sheaf functor along an open embedding is full and faithful` returned eight
results about open immersions of sheafed spaces and ordinary pushforwards.  Neither is
the small pro-etale extension-by-zero statement.  Direct `rg` with `fully faithful`,
`FullyFaithful`, and `extension.*zero` in Mathlib's Sites directory, upstream pro-etale
lower-shriek modules, and `lean/Sheaf` found the exact upstream declaration above and
no replacement needed for it.

I also read `coord/pefw-upstream-framework.md` and the exact shared side-project source
under `lean/WeilConjectures/`.  Its fully-faithful declaration and binders agree with the
older source just checked.  The recorded definition dependency now names
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
there `openImmersionLowerShriek` (lines 295--299) uses the real construction
`localizationLowerShriek A j inferInstance`, and `localizationLowerShriek_eq` (240--245)
identifies it with the inclusion of sheaves, left Kan extension, and sheafification.
The compatibility module re-exports this canonical definition.  Thus the updated module
path does not change the notion.  The node's source is a blueprint Markdown lemma,
not a Stacks tag; I read that exact lemma, its extension-by-zero definition, and their
parent unit, which explicitly fixes Grothendieck abelian coefficients.  No repair note,
new definition node, dependency module, or statement correction applies to this item.

Validation: `deliver2.py Q28 lem-sfb-finite-extension-by-zero-fully-faithful --no-push`
printed `OK (dry run)` at commit `fa55bbc834`: preflight passed and the existing-declaration
probes compiled cleanly through the prescribed single-file compilation wrapper.  There
are no new Lean files to compile in this delivery.
