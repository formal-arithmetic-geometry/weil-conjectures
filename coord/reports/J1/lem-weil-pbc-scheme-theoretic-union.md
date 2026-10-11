## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion` states
`AlgebraicGeometry.scheme_theoretic_union`. It uses Mathlib's scheme type,
closed-immersion predicate, ideal sheaf kernel `i.ker`, and affine spectrum.
For closed immersions `i' : Z' ⟶ X` and `i'' : Z'' ⟶ X`, the intersection
`i'.ker ⊓ i''.ker` is the quasi-coherent ideal sheaf defining the union. The
statement renders each clause as follows:

* The first conjunct says that its canonical closed subscheme morphism
  `(i'.ker ⊓ i''.ker).subschemeι` is a closed immersion.
* The second says its ideal sheaf kernel is exactly `i'.ker ⊓ i''.ker`.
* The affine-local description is rendered by the `IsPullback` conjunct: on every
  `U : X.affineOpens`, the subscheme cover map is the pullback of
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ...))`, where the quotient ideal
  is `(i'.ker ⊓ i''.ker).ideal U`.
* The underlying image clause is
  `Set.range (i'.ker ⊓ i''.ker).subschemeι.base = Set.range i'.base ∪
  Set.range i''.base`.
* The final two conjuncts provide closed immersions `a'` and `a''` and the
  factorisation equations `a' ≫ i''' = i'` and `a'' ≫ i''' = i''`, with
  `i''' = (i'.ker ⊓ i''.ker).subschemeι`.

The proof is left as `sorry`, as required at stage 2. Its intended stage-3 route
is the three proof steps in the node: (1) use
`lem-weil-pbc-quasi-coherent-ideal-intersection` and
`lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`; (2) use
`lem-weil-pbc-affine-open-spec-points`,
`lem-weil-pbc-closed-immersion-image-zero-locus`, and
`lem-weil-pbc-zero-locus-ideal-intersection` to identify the image on affine
opens and then cover `X`; (3) use
`lem-weil-pbc-closed-immersion-factor-ideal-inclusion` for the two factors.
The dependency declarations used directly by the module are Mathlib's
`AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsClosedImmersion`,
`AlgebraicGeometry.Scheme.Hom.ker`, and
`AlgebraicGeometry.Spec` (the recorded declarations for the four statement
dependencies).

Edge cases checked: the construction permits `Z'` or `Z''` to be empty and the
intersection ideal to be `⊤`; it also permits either ideal to be `⊥`, and no
nonemptiness or finiteness assumption is introduced. The affine-local clause is
quantified over all affine opens, including the empty scheme case.

Searches made:

* `msearch.py ... leanfinder "scheme theoretic union two closed subschemes intersection ideal sheaves"`: returned `IdealSheafData.vanishingIdeal_sup`, `vanishingIdeal_iSup`, and affine zero-locus lemmas, but no theorem for the closed subscheme union.
* `msearch.py ... loogle "Scheme.IdealSheafData.subschemeι IsClosedImmersion Set.range"`: 0 hits (the identifier was unknown to Loogle).
* `msearch.py ... grep "scheme_theoretic_union|support_inf|IdealSheafData.*subscheme" Mathlib/AlgebraicGeometry`: 0 hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no existing scheme-theoretic-union declaration; it found only the generic `IdealSheafData.inclusion` usages and unrelated prose.
* `grep` for the node id in `WeilConjectures/` found no source declaration.
* `tools/blueprint_refs.py search lem-weil-pbc-scheme-theoretic-union` found no blueprint node.

No new nodes or dependency modules were needed; all four statement dependencies
have usable recorded declarations. No statement correction or disputed statement
was necessary.

## Second reading by J1

The node introduces the following objects and clauses. `X : Scheme` is rendered
by `{X Z' Z'' : Scheme.{u}}`; the two maps `i' : Z' ⟶ X` and
`i'' : Z'' ⟶ X` are explicit morphisms, with exactly the two hypotheses
`[IsClosedImmersion i']` and `[IsClosedImmersion i'']`. Their ideal sheaves are
rendered by `i'.ker` and `i''.ker`, using the recorded Mathlib declaration
`Scheme.Hom.ker`. The intersection is `i'.ker ⊓ i''.ker`. Its canonical closed
subscheme morphism is `(i'.ker ⊓ i''.ker).subschemeι`; the first three
conjuncts state respectively that this is a closed immersion, that its kernel
is the intersection, and the affine-local quotient-spectrum pullback description
for every `U : X.affineOpens`. These conjuncts render the node's "let `i'''`"
construction and its stated affine description. Clause (a) is rendered exactly
as equality of ranges of the underlying maps and union of ranges. Clause (b) is
rendered by the two existential factor maps, each carrying `IsClosedImmersion`
and the required composition equation. Objects, hypotheses, conjunction order,
and quantifier order all match the node; no extra finiteness, separation,
Noetherian, characteristic, or universe restriction was introduced.

Edge cases: `Scheme.{u}` includes empty schemes; either source scheme may be
empty; either ideal may be `⊤` or `⊥`; the infimum and quotient are still defined.
The affine-open quantifier includes empty affine opens. No index set, integer
parameter, characteristic, or nonemptiness assumption occurs.

I rechecked the three searches recorded above against Mathlib and
`WeilConjectures/`; no existing declaration states this theorem, and no
additional definition or dependency module is needed. I also read the recorded
dependency signatures (`Scheme`, `IsClosedImmersion`, `Scheme.Hom.ker`, and
`Spec`) and verified that each is the notion used by the node. The Stacks
Definition 0C4H and Lemma 0C4J agree with the intersection ideal, quotient
affine description, underlying-set union, and closed-immersion factor maps.
There was no mismatch to repair. Compilation with `scompile.py` succeeds with
only the permitted `sorry` declaration warning.

Source read: the local Stacks checkout is absent on this machine, so the official
[Definition 0C4H](https://stacks.math.columbia.edu/tag/0C4H) and
[Lemma 0C4J](https://stacks.math.columbia.edu/tag/0C4J) were opened and read.
The former defines the union by ideal intersection; the latter gives the two
closed immersions and the affine intersection ideal used here. No node correction
is needed.

Additional searches: LeanSearch query `scheme theoretic union of two closed
subschemes intersection of ideal sheaves` was unavailable (Internal Server Error).
The initial grep used the wrong subdirectory and its zero result is not evidence;
the corrected grep query `support_inf|scheme_theoretic_union|def subscheme|range_subschemeι|subschemeι`
in `AlgebraicGeometry` returned the subscheme construction, its image lemma, and
closed immersion instance; none states this combined theorem.

Quasi-coherence and intersection are rendered by the type `X.IdealSheafData` of
`i'.ker ⊓ i''.ker`; its `ideal` on each affine open is definitionally the infimum
of the two ideals (Basic.lean, `ideal_inf`). Thus the quotient appearing in the
pullback conjunct is precisely `Γ(X,U) / (I ∩ J)`. There is no separate choice of
a potentially different union subscheme.

Dependency sources read: `Mathlib.AlgebraicGeometry.Scheme` for `Scheme` and
`Spec` / `Spec.map`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` for
`IsClosedImmersion`; `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` for `Hom.ker`,
`Hom.ker_apply`, the `IdealSheafData` structure and its infimum; and
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` for the canonical closed subscheme.
