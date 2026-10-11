## Worker report

The item is already stated exactly by Mathlib's
`AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc` in
`Mathlib/AlgebraicGeometry/Morphisms/Basic.lean` (line 305), so no module is added.
The declaration is the generic statement
`lemma sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}}
{f : ∀ i, Y i ⟶ X} (hf : ∀ i, P (f i)) : P (Sigma.desc f)`
under `[IsZariskiLocalAtSource P]`.  Taking `P := @AlgebraicGeometry.Etale` gives the
node's conclusion.  Mathlib's `Etale` morphism property has an
`IsZariskiLocalAtSource` instance via `HasRingHomProperty`; this is the instance in
`Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`.  Taking `ι = I` and using the finite
index hypothesis gives the required `Small` instance.  `Sigma.desc f` is the induced
coproduct morphism, and `Sigma.ι_desc` gives its restriction equation
`Sigma.ι f i ≫ Sigma.desc f = f i`.

The node hypotheses and clauses correspond as follows: `X` is the target scheme;
`I` is the finite family index type; `Y i` is `U_i`; `f i` is `u_i`; each
`Etale (f i)` is the hypothesis `hf`; and `Etale (Sigma.desc f)` is the conclusion
that the induced coproduct morphism is etale.  The generic theorem also permits an
arbitrary small index type, hence includes finite families and the empty family.

Dependencies used: `def-pc-scheme` is Mathlib's `AlgebraicGeometry.Scheme`;
`def-weil-etale-morphism` is Mathlib's `AlgebraicGeometry.Etale`;
`lem-weil-pbc-scheme-coproduct-family` supplies the coproduct and coprojections,
represented by `HasColimitsOfShape (Discrete I) Scheme`, `Sigma.desc`, and
`Sigma.ι_desc` in `Mathlib/AlgebraicGeometry/Limits.lean` and
`Mathlib/CategoryTheory/Limits/Shapes/Products.lean`.

Edge cases checked: the empty finite index type is covered by the universal
quantifier in `hf` and by the generic coproduct theorem; a singleton family reduces
to the given morphism; arbitrary finite index types are allowed, with no universe
restriction beyond Mathlib's `Small` parameter.

Searches made: `msearch.py ... leanfinder "A finite coproduct of etale morphisms of schemes is etale"`
returned `IsZariskiLocalAtSource.sigmaDesc` as the relevant generic theorem (and no
more specialized theorem); `msearch.py ... loogle "AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc"`
returned its exact signature; `msearch.py ... grep "sigmaDesc|Etale.*(coprod|sigma|desc)" AlgebraicGeometry`
found the theorem at `Morphisms/Basic.lean:305` and the coproduct infrastructure;
`rg` over Mathlib, `WeilConjectures`, and existing `lean/Sheaf` found no project
statement of this item.  The node's stage-1 lead note independently identifies the
same Mathlib declaration.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the existing-declaration record above was
checked against the Mathlib signature and the node clause by clause.

## Second reading by G1

I independently opened the sandbox node, Mathlib's declaration and its ambient
binders in `Morphisms/Basic.lean`, every statement dependency and its recorded
Mathlib declarations, and the source at `definition-etale` and
`lemma-etale-characterize` in `/home/ubuntu/c1-stacks-review/morphisms.tex`
(the locally available Stacks source; the repository's literature checkout is
absent). The source introduces arbitrary schemes and scheme morphisms; it
explicitly imposes neither separation nor quasi-compactness. Its (1) iff (3)
with the trivial target covering is the precise source-locality assertion used
by this node.

The complete object/hypothesis/conclusion inventory and its Lean rendering:

- Target scheme X: `{X : Scheme.{u}}`. Verdict: the same arbitrary scheme.
  I read `Scheme` and `Scheme.Hom` in `AlgebraicGeometry/Scheme.lean`:
  schemes are locally ringed spaces locally isomorphic to spectra of commutative
  rings, and morphisms are morphisms of locally ringed spaces. These are the
  notions recorded by `def-pc-scheme`, not varieties or affine schemes.
- Finite index set I: `{ι : Type v}` with the node's finiteness supplied as
  `[Finite ι]` when specializing. The generic declaration requests `[Small.{u} ι]`.
  Verdict: no additional hypothesis on a finite family; server typeclass
  synthesis supplies `Small.{u} ι` from `Finite ι` at independent universes u,v.
  The declaration is more general, but its recorded finite-family specialization
  has exactly the node's hypotheses, as permitted for existing declarations.
- Source schemes U_i: `{Y : ι → Scheme.{u}}`. Verdict: arbitrary schemes,
  exactly as in the node, without affine, nonempty or finiteness conditions.
- Component morphisms u_i: `{f : ∀ i, Y i ⟶ X}`. Verdict: the same family with
  common target, and the same quantifier order.
- Each component is etale: `(hf : ∀ i, P (f i))` specialized to
  `P := @AlgebraicGeometry.Etale`. Verdict: exact. I read the `Etale` class,
  its `HasRingHomProperty` instance, and `Etale.iff_flat_and_formallyUnramified`
  in `Morphisms/Etale.lean`. The latter equivalence and the diagonal-open-immersion
  statements in `Morphisms/FormallyUnramified.lean` reconcile the affine-local
  ring-map definition with `def-weil-etale-morphism`'s flat, locally finitely
  presented, unramified definition. No stronger notion is substituted.
- Coproduct V and its inclusions: `∐ Y` and `Sigma.ι Y i`. Verdict: the same
  categorical coproduct. I read the small-index `HasColimitsOfShape (Discrete ι)
  Scheme` instance, `sigmaOpenCover` and `disjoint_opensRange_sigmaι` in
  `AlgebraicGeometry/Limits.lean`, as recorded by
  `lem-weil-pbc-scheme-coproduct-family`. These supply the open, disjoint,
  covering coprojections, with the clopen consequence given in the node.
- Induced u with restrictions u_i: `Sigma.desc f`, with
  `Sigma.ι_desc f i : Sigma.ι Y i ≫ Sigma.desc f = f i`.
  Verdict: exact defining equations, read in `Limits/Shapes/Products.lean`.
  `Sigma.hom_ext` gives uniqueness, so naming the canonical morphism neither
  adds a choice hypothesis nor omits an arbitrary morphism satisfying these
  equations; another presentation of the coproduct is transported by its
  canonical isomorphism, and the locality property respects isomorphisms.
- Conclusion u is etale: `P (Sigma.desc f)` with P specialized as above.
  Verdict: exactly `Etale (Sigma.desc f)`, with no extra conclusion.
- Ambient `[IsZariskiLocalAtSource P]`: verdict: no extra geometric assumption.
  I read `HasRingHomProperty.instIsZariskiLocalAtSource` in
  `Morphisms/RingHomProperties.lean`; it applies to the existing Etale instance.
  Server synthesis confirms this specialized instance.

The node's proof also matches the existing declaration: the coprojections give
an open cover of V; their composites with `Sigma.desc f` are f i by
`Sigma.ι_desc`; apply the source-cover equivalence (the generic declaration uses
`iff_of_openCover`) and hf. I opened the proof dependency
`lem-weil-pbc-etale-local-on-source` and its match
`IsZariskiLocalAtSource.iff_of_iSup_eq_top`, whose signature is exactly the stated
open-source-cover equivalence. The empty-family argument is vacuous. No new node,
new definition, dependency module, statement correction, hollow definition or
new theorem proof occurs in this delivery. The existing Mathlib declaration is
reused without imposing project docstring requirements on upstream Mathlib.

Edge cases: the empty finite index set is allowed (there is no Nonempty
instance); its coproduct is the empty scheme and hf is vacuous. A singleton
family is included. Empty source components and an empty target are permitted
whenever the specified component morphisms exist. No field, characteristic,
Noetherian, separated or quasi-compact assumption occurs. There is no numerical
n or additive zero object in this statement. Independent universes u,v are
accepted, including finite indices in higher universes; finite families of
schemes can be placed in a common scheme universe.

Independent searches, using different phrasing from the first worker:

- `msearch.py ... leansearch "A morphism from a disjoint union of schemes is
  etale if its components are etale"`: service returned Internal Server Error;
  unavailability recorded, no mathematical verdict inferred from it.
- `msearch.py ... leanfinder "Properties local on the source are preserved by
  the map from a disjoint union"`: found the existing
  `AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc` and related locality lemmas.
- `msearch.py ... loogle '"sigmaDesc"'`: returned its full type, including the
  ambient morphism property, locality instance and independent index universe.
- `msearch.py ... grep 'sigmaDesc|small.*[Ff]inite|[Ff]inite.*small'
  AlgebraicGeometry`: found `Morphisms/Basic.lean:305` and coproduct machinery.
  Additional `rg` searches for sigmaDesc and etale/disjoint-union or coproduct
  combinations in Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
  and the repository's `lean/Sheaf` found no alternative exact specialized
  statement. The existing project theorem
  `etale_sigmaDesc_spec_of_finite_separable`, which I opened, only concerns
  spectra of finite separable field extensions and is not this general node.

Validation: the scratch-only `scratchpad/Specialization.lean` imports Etale,
sets autoImplicit false, explicitly binds u,v,X,I,U,f with `[Finite I]`, synthesizes
both required instances, and checks the lambda from hf to
`Etale (Sigma.desc f)` plus the restriction equation, uniqueness signature and
Etale equivalence. `scompile.py G1 lem-sc-etale-coproduct-etale` on that file
returned exit code 0, compiled in 1.7 seconds, with no warnings. This scratch file
is not a delivery module and contains no new theorem declaration. I compared
`lean.statement` verbatim with the signature in Basic.lean: it is unchanged and
matches. No mathematical mismatch was found; only this independent report and
scratch validation were added. The Worker report remains in place.
