## Worker report

The node is already stated by the existing upstream theorem
`AlgebraicGeometry.exists_isDense_compactification` in
`WeilConjectures.Compactification.Dense`; no new Lean module is needed.  The recorded
companion declaration `AlgebraicGeometry.Compactification.quasiCompact_openImmersion`
in `WeilConjectures.Compactification.Defs` supplies the quasi-compactness of the open
immersion required by the dependency notion.

The theorem signature is:

```lean
theorem exists_isDense_compactification [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ c : Compactification f, c.IsDense :=
```

Here `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)` are the surrounding binders in the
source module.  `[CompactSpace Y]` and `[QuasiSeparatedSpace Y]` render the node's
quasi-compact and quasi-separated hypotheses on the base.  Under the project's scheme
convention, `[LocallyOfFiniteType f]` together with `[QuasiCompact f]` is exactly
“of finite type”; `[IsSeparated f]` renders separatedness.  The existential conclusion
provides a compactification `c : Compactification f`, whose `c.IsDense` field says
that its open immersion is scheme-theoretically dominant, hence scheme-theoretically
dense.  The companion `quasiCompact_openImmersion` gives `QuasiCompact c.i`, so the
quasi-compact open immersion in `sk-def-nagata-sketch-data` is present.

The dependency declaration used is `AlgebraicGeometry.Compactification.BoundaryCompactification`
and related data from `Sheaf.Compactification.BoundaryRefinement`; the theorem itself
uses the upstream `AlgebraicGeometry.Compactification` and
`AlgebraicGeometry.Compactification.IsDense` from
`WeilConjectures.Compactification.Defs` and `Dense`.

Edge cases checked: the theorem permits arbitrary schemes `X` and `Y` in one universe,
including empty `X`; a proper `f` is covered by the identity compactification; and the
quasi-compactness condition on the open immersion is not silently omitted, since it is
derived by `quasiCompact_openImmersion` from `[QuasiCompact f]`.  No extra condition on
`X` or on the characteristic is present.

Searches made: `msearch.py ... leanfinder` for “Every separated morphism of finite type
over a quasi-compact quasi-separated scheme admits a dense compactification” returned
constituent morphism-property hits and no competing theorem.  `msearch.py ... loogle`
for `AlgebraicGeometry.exists_isDense_compactification,
AlgebraicGeometry.Compactification.quasiCompact_openImmersion` returned no hits because
Loogle marked the upstream name unknown.  Direct `rg` in `WeilConjectures` found the
exact declarations in `Compactification/Dense.lean` and `Compactification/Defs.lean`.
The existing declarations therefore match the node and are recorded with
`existing: true`.

## Earlier second reading (a previous round; superseded)

I independently read the node and the source declarations.  The base hypotheses map
as follows: node “quasi-compact” and “quasi-separated” are respectively
`[CompactSpace Y]` and `[QuasiSeparatedSpace Y]`; node “separated” is
`[IsSeparated f]`; and node “finite type” is the pair
`[LocallyOfFiniteType f] [QuasiCompact f]`, the established morphism convention.
The conclusion's `∃ c, c.IsDense` is exactly a factorization by an open immersion and a
proper morphism with scheme-theoretically dominant open immersion.  Reading
`quasiCompact_openImmersion` confirms that the open immersion is quasi-compact under
`[QuasiCompact f]`.  No hypothesis, object, or conclusion clause is added or omitted,
and no statement correction or new node is needed.

## Second reading by Q90

I independently opened the item node, its exact main-20261015 `_section.md`,
`sk-def-nagata-sketch-data`, the recorded dependency module
`Sheaf.Compactification.BoundaryRefinement`, and the upstream modules
`WeilConjectures.Compactification.Dense` and `Defs`. There is no repair note for
this item. There is no statement correction, dependency repair, or new node in
this delivery.

Source check: Stacks tag 0F41 maps to `flat-theorem-nagata`, in `flat.tex`, not
the algebraic-space theorem with the same local label in `spaces-pushouts.tex`.
I read the scheme theorem and the preceding Compactifications section. The
standing assumptions are precisely that S is a quasi-compact, quasi-separated
scheme and X -> S is separated of finite type. No Noetherian, reducedness,
characteristic, or finite-presentation assumption persists in the theorem.
The preceding `lemma-compactifications-cofiltered`, part (b) and its proof,
obtains scheme-theoretic density by schematic closure. This is exactly the
dense form stated in the blueprint node; the source needs no correction.

The node's complete object/hypothesis/conclusion list, matched with Lean:

1. Schemes X and S: the source's surrounding binders are
   `{X Y : Scheme.{u}}`, with Y rendering S. Verdict: the same schemes;
   `u` is arbitrary, with no field or base-scheme parameter imposed.
2. A given morphism f : X -> S: the theorem's explicit `(f : X ⟶ Y)`
   comes from `variable (f) in`. Verdict: quantified before its properties
   and before the existential compactification, as in the node.
3. S quasi-compact: `[CompactSpace Y]`. Verdict: precisely quasi-compactness
   of the underlying space; no Hausdorff condition is part of `CompactSpace`.
4. S quasi-separated: `[QuasiSeparatedSpace Y]`. Verdict: precisely the
   scheme's quasi-separatedness, with no separatedness of S added.
5. f separated: `[IsSeparated f]`. Verdict: same relative property.
6. f finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`. Verdict:
   exactly finite type, not finite presentation; no Noetherian assumption.
7. Existence of an ambient scheme and factorization: `∃ c : Compactification f,
   c.IsDense`, where `c.Z : Scheme.{u}`, `c.i : X ⟶ c.Z`,
   `c.g : c.Z ⟶ Y`, and `c.comm : f = c.i ≫ c.g`.
   Verdict: the existential follows all the given data and hypotheses;
   the factorization equality has the correct composition order.
8. Open immersion j: `c.isOpenImmersion : IsOpenImmersion c.i` is a field
   of the existing `Compactification`. Verdict: exactly the required map.
9. Quasi-compactness of j: for every such c, the recorded companion theorem
   `c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)` supplies
   `QuasiCompact c.i`. Verdict: this clause is available for the very same
   existential witness, without replacing it or strengthening the hypotheses.
   It is important that upstream `Compactification` alone omits this condition;
   the companion theorem is part of the recorded binding for that reason.
10. Properness of p: `c.isProper : IsProper c.g` is a field. Verdict: proper
    over S, with no projectivity, smoothness, or other condition added.
11. Scheme-theoretic density: `c.IsDense` unfolds to
    `IsSchemeTheoreticallyDominant c.i`, whose definition is `c.i.ker = ⊥`.
    With the quasi-compactness in item 9, `Scheme.Hom.app_injective` gives
    injectivity on every open of c.Z, hence injectivity of
    O_(c.Z) -> j_* O_X. Conversely, injectivity gives zero kernels on affine
    opens, hence the same kernel-ideal equality. Verdict: the node's density,
    not merely topological density; no reducedness hypothesis is needed.

Dependency interface checked: `BoundaryCompactification f` is a
`WideSubcategory` whose objects wrap `QuasiCompactObjects f`;
`QuasiCompactObjects f` is the existing `Compactification f` with the property
`QuasiCompact c.i`. `DenseBoundaryCompactification f` further wraps the
property `IsSchemeTheoreticallyDominant c.obj.obj.i`. Opening Mathlib's
`FullSubcategory` and `WideSubcategory` structures confirms that these wrappers
introduce no additional object data or object-side hypotheses. Refinement
conditions belong to morphisms; this existence node asserts no refinement.
Thus the original report's reference to the dependency is a semantic use of
these same objects, not a claim that upstream Dense imports the side module.
The dependency needs no replacement module.

I verified this interface by compiling a scratch consumer that takes
`⟨c, hc⟩` from `exists_isDense_compactification f` and returns
`Nonempty (Compactification.DenseBoundaryCompactification f)` using exactly
`c.quasiCompact_openImmersion inferInstance` and `hc`. A second scratch
consumer checks `Function.Injective (c.i.app U)` on every open U. No new
construction, theorem, or proof is delivered: these are scratch checks only.
The first scratch run exposed only `haveI` style warnings, corrected to `have`
for the clean rerun. All compiles use the prescribed `scompile.py` wrapper.
`#print axioms` for both recorded existing theorems lists only `propext`,
`Classical.choice`, and `Quot.sound`.

Edge cases: empty X is admitted without a Nonempty instance; density then
forces the ambient scheme to be empty. Empty S entails empty X and is also
included. For proper f the identity compactification satisfies the conclusion.
Nonreduced schemes are included, so replacing scheme-theoretic density by
ordinary density would have been wrong; the actual predicate retains it.
No index set, integer degree, or coefficient characteristic occurs. The one
arbitrary scheme universe covers all schemes in a common universe; there is
no independent test-object universe or extra universe equality. All binders
are bound in the existing source; no auto-implicit variable is being inferred.

Independent searches (logged in `searches.jsonl`): LeanSearch for
"Existence of a scheme theoretically dense compactification of a separated
finite type morphism of schemes with quasi compact quasi separated target"
returned 8 constituent-property hits, including quasi-compactness and
quasi-separatedness equivalences, but no competing compactification theorem.
LeanFinder for "For a separated quasi compact scheme morphism locally of finite
type over a qcqs base there is a proper ambient scheme containing the source as
a schematically dense open subscheme" returned 8 properness/normalization hits,
no exact theorem. Loogle for `"compactification"` and the wrapper's grep for
`dense compactification` each returned zero hits. I also searched directly
with `rg` for `exists.*compactification`, `compactification.*exists`,
`NagataCompactification`, `DenseBoundaryCompactification`, and
`schematically dense` throughout upstream `WeilConjectures` and project
`lean/Sheaf`, and for `nagata|compactif|scheme.theoretically dense` in Mathlib's
AlgebraicGeometry directory. These searches locate the exact upstream theorem,
its chosen compactification, its properness/open/density definitions, and the
side category wrappers already discussed. Mathlib has constituent notions but
no independent Nagata existence theorem. The upstream-name table was checked
for the recorded existence name and `NagataCompactification`; the latter is
listed, consistent with the direct source reading. Writing another theorem
module here would duplicate the already available result.

Findings and changes: no mathematical mismatch found. I retained the existing
Lean binding and its verbatim source signature. I added this independent
reading, made the quasi-compactness bridge and dependency-object wrappers
explicit, and supplied scratch compilation/axiom evidence. No Lean module,
node statement, definition, dependency list, or target statement changed.
