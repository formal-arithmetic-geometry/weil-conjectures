## Worker report

The module states `AlgebraicGeometry.noetherian_perfect_directImage` in
`lean/Sheaf/AlgebraicGeometry/NoetherianPerfectDirectImage.lean`. It uses the existing
scheme, morphism, derived category, derived direct image, perfect complex, and proper-support
notions recorded by the six statement dependencies.

The binders render the node as follows. `S` is a scheme with `[IsNoetherian S]`; `f : X ⟶ S`
has `[LocallyOfFinitePresentation f]`, `[QuasiCompact f]`, and `[QuasiSeparated f]`. The four
`HasDerivedCategory` binders provide the derived categories on X and S and on every open of X
and S. `E : schemeDerivedCategory X` with `hE : Scheme.IsPerfect X E` is the perfect object.
`G` is a cochain complex of O_X-modules. `hGb` gives integers `a,b` outside which every term
is zero. The typeclass binder gives finite presentation of every term. `hGflat` states
`Scheme.Modules.IsFlatOver (G.X n) f` for every degree, and `hGproper` states
`Scheme.Modules.HasSupportProperOver f (G.X n)` for every degree. The conclusion is exactly
that `(schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)` is perfect on S.
The tensor uses the project's global derived tensor structure.

Dependencies used: `Mathlib.AlgebraicGeometry.Scheme` (`AlgebraicGeometry.Scheme` and
`Scheme.Hom`); `Sheaf.AlgebraicGeometry.DerivedCategory`
(`AlgebraicGeometry.schemeDerivedCategory`); `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`
(`AlgebraicGeometry.schemeDerivedDirectImage`); `Sheaf.AlgebraicGeometry.PerfectComplex`
(`AlgebraicGeometry.Scheme.IsPerfect`); and
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
(`AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`).

Edge cases checked: the bounded range permits `a = b` and the zero complex; quantification over
all integer degrees is retained; no nonemptiness or positivity assumption is imposed on the
range; arbitrary schemes and empty opens remain allowed by the open-derived-category binders.

Searches made: `msearch.py leanfinder` for the Noetherian perfect direct-image statement found
only generic Tor/flatness declarations; `msearch.py loogle` for `AlgebraicGeometry.Scheme,
DerivedCategory` found no hits; `msearch.py grep` for `perfect.*direct.image|direct.image.*perfect`
in Mathlib AlgebraicGeometry found no hits. `rg` over the source and project found no existing
declaration for this node. The source statement was checked against Stacks Tag 0DJQ.

## Second reading by Q1

Independently read the item node, its six statement-dependency nodes and the actual
recorded declarations, then the delivered theorem. The source checkout of the Stacks
TeX is not installed in this repository snapshot, so I read the official Stacks Tag
0DJQ page and fetched `perfect.tex` from the official stacks/stacks-project repository
into sandbox scratch. Read section `section-producing-perfect`, especially
`lemma-tensor-perfect` (Tag 0DJQ) and the preceding `lemma-perfect-direct-image`
(Tag 08EV). This section assumes no extra base field, characteristic, separatedness
or flatness of the morphism. The source lemma allows locally finite type morphisms;
the node intentionally takes the finite-presentation specialization. Its finitely
presented terms are coherent because X is locally Noetherian. This is a legitimate
specialization already present in the node, not an additional Lean hypothesis.

The object/hypothesis/conclusion checklist is:

1. Schemes X and S: `{X S : Scheme.{u}}`. Read Mathlib's `Scheme` structure and the
   scheme/morphism dependency. These are general schemes, not varieties. PASS.
2. S Noetherian: `[IsNoetherian S]`. Read Mathlib's class: locally Noetherian and
   quasi-compact, exactly the global Noetherian hypothesis. No Noetherian hypothesis
   on X is added. PASS.
3. f of finite presentation: `(f : X ⟶ S)` with `[LocallyOfFinitePresentation f]`,
   `[QuasiCompact f]`, `[QuasiSeparated f]`. Read the morphism-conventions dependency,
   which explicitly defines finite presentation as this triple, and Mathlib's three
   class signatures. No separatedness, properness or flatness of f is assumed. PASS.
4. E_i perfect on X: `(E : schemeDerivedCategory X)` and
   `(hE : Scheme.IsPerfect X E)`. The node's subscript names one object, with no
   quantified family or condition on an index. Read `schemeDerivedCategory` and
   `Scheme.IsPerfect`/`IsStrictlyPerfect`: all O_X-module sheaves, with local bounded
   finite-free direct-summand representatives. This is the recorded notion. PASS.
5. G a complex of O_X-modules: the explicitly shared carrier in
   `(G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)`.
   This is the same carrier/category used by the derived-category dependency,
   not a second category structure on the `X.Modules` abbreviation. PASS.
6. G bounded: `hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n)`.
   Every degree outside a finite integer interval vanishes as a module object;
   this is boundedness of terms, not merely bounded cohomology. PASS.
7. G finitely presented: `[∀ n : ℤ, (G.X n).IsFinitePresentation]`. Read Mathlib's
   sheaf class in `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`: local finite
   presentations as cokernels of maps of finite free modules. It supplies
   quasi-coherence and finite type. On this locally Noetherian X this is equivalent
   to the source's coherence condition. PASS.
8. G flat over S: `hGflat : ∀ n : ℤ, Scheme.Modules.IsFlatOver (G.X n) f`.
   Read the upstream definition in `Cohomology/DirectImage/Basic.lean`: sections on
   affine U over affine V are flat over Γ(S,V) via f.appLE. With the quasi-coherence
   from item 7 this is equivalent to relative stalkwise flatness, hence the source's
   f-inverse-image-O_S flatness. It does not demand O_X-flatness of G. PASS.
9. G with support proper over S: `hGproper : ∀ n : ℤ,
   Scheme.Modules.HasSupportProperOver f (G.X n)`. Read both declarations in
   `ClosedSubsetProperOverBase.lean`: exactly the nonzero-stalk locus is closed and
   its reduced induced closed subscheme is proper over S. Since G is bounded, its
   union of term supports is a finite union; termwise proper support and properness
   of that union are equivalent (closed subsets and finite unions of proper closed
   subsets). No properness of X is imposed. PASS.
10. Conclusion: `Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
    (E ⊗ DerivedCategory.Q.obj G))`. Read the recorded scheme direct image and its
    ringed-space implementation: K-injective right derived module pushforward.
    `Q.obj G` is the derived object of this very complex. Read the shared global
    `schemeDerivedTensorMonoidal`: the K-flat derived tensor of module sheaves.
    The conclusion has exactly perfectness of Rf_*(E tensor^L G) and no extra clause.
    PASS.

The four `HasDerivedCategory.{w}` binders provide localization models for X, S and
all their opens, required by these recorded declarations. They impose no geometric
or finiteness condition. u and w are explicitly bound, and a common enlarged universe
accommodates the schemes, module sheaves and their localization models; no test-object
quantifier at an independently smaller universe occurs. All variables are bound.

Edge cases: empty X, empty S whenever a morphism exists, and empty opens are permitted.
Perfectness on empty X is its correct pointwise vacuous condition. The zero complex
satisfies any chosen finite bounds; the zero perfect object is allowed. Bounds may
coincide, and a > b allows the entirely zero complex. Degree 0 and negative degrees
are included; no positivity, nonempty index set, base field or characteristic
restriction appears. A zero term has empty support, which the recorded predicate
permits. No edge-case exclusion found.

Independent H4 searches (queries and service answers recorded in searches.jsonl):
LeanSearch, "A bounded coherent complex flat over the base with proper support tensored
with a perfect complex has perfect derived pushforward", was unavailable (Internal
Server Error). LeanFinder, "Tensoring a locally finite projective complex with a
relatively flat coherent complex and pushing forward over a noetherian scheme produces
a perfect complex", returned generic module-flatness, Tor and condensed-projectivity
results, none matching. Loogle, `"IsPerfect"`, returned unrelated perfect pairing and
matching results. Mathlib grep `IsPerfect|proper.support|finite.tor.dimension` under
AlgebraicGeometry returned no hits. Independently rg-searched the project and upstream
sources with `perfect.*(pushforward|directimage|direct_image)` and the reverse order,
plus `0DJQ`; searched upstream names for `Rf_.*perfect|perfect.*Rf_` and Noetherian
pushforward terms. The project's proper-support theorem has a non-Noetherian base and
adds a base-change clause; its proper-perfect theorem instead assumes a proper perfect
morphism. Opened those signatures and the perfect-base-change module: none is this
statement. No exact existing declaration, private definition or missing notion found.
No new nodes, dependency modules or statement correction are in this delivery.

H5/H6/H8/H9: the module adds no definitions or instances; its sole theorem proof is
`sorry`. Both docstrings give Tag 0DJQ and the blueprint id. The statement docstring
faithfully carries all four node proof steps: bounded coherence, proper supports,
finite relative Tor dimension, then Tag 08EV. Imports serve the actual notions used;
there is no file-local notation, private copy, hidden let or unbound variable.
Verified the node's lean.statement equals the complete source signature verbatim.
Local single-file compilation with lcompile.py succeeded in 4.4 seconds, exit 0,
with no warnings. Delivery dry run supplies the final server compile and preflight.

Mismatches found: none. Changed only this report by appending the independent reading;
the correct theorem module and node record are preserved.
