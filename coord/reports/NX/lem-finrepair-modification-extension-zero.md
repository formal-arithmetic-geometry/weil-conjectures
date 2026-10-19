## Worker report

The module `Sheaf.AlgebraicGeometry.ModificationExtensionZero` states
`AlgebraicGeometry.Etale.modification_extension_zero`, with one whole-proof `sorry`.
No definitions, dependency modules, or new nodes are introduced. No natural-language
statement correction is needed.

Hypothesis and conclusion correspondence:

- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- The three schemes are `{Y U X : Scheme.{u}}`; the proper map is
  `(π : Y ⟶ X) [IsProper π]` and the open immersion is
  `(j : U ⟶ X) [IsOpenImmersion j]`.
- The chosen `U'` is `pullback π j`, with `j' = pullback.fst π j` and
  `h = pullback.snd π j`. The hypothesis on `h` is `[IsIso (pullback.snd π j)]`.
  These are the actual fibre product projections, with no additional square or
  compatibility hypotheses. The first projection is an open immersion by base change.
- An arbitrary coefficient sheaf is
  `(G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. There is no finite-stalk,
  constructibility, local-constancy, or coefficient-invertibility hypothesis.
- `G'` is `(upperStar (ModuleCat.{u + 1} Λ) (pullback.snd π j)).obj G`.
- `j'_!G'` in the vanishing conclusion uses the recorded `openImmersionLowerShriek`
  applied to `pullback.fst π j`. The base-change map uses `etaleLowerShriek`;
  for these open immersions it is definitionally the same functor as
  `openImmersionLowerShriek`: both are the sheafified left Kan extension along
  `MorphismProperty.Over.map`. In particular the canonical map has exactly the
  source `j_!G` and target `π_*j'_!G'` specified in the node.
- The first conjunct is `IsIso` of the image of the inverse base-change component
  under `(upperStarLowerStarAdjunction (ModuleCat Λ) π).homEquiv _ _`.
  The inverse is obtained from the natural transformation
  `etaleLowerShriekBaseChangeMap Λ π j`, using the named proof
  `isIso_etaleLowerShriekBaseChangeMap Λ π j` explicitly in `@inv`.
  This fixes the actual canonical adjunction map, rather than asserting the existence
  of some isomorphism between the two sheaves. The underscore arguments are inferred
  source and target objects, not unbound variables or missing hypotheses.
- The second conjunct is `∀ q : ℤ, 0 < q → IsZero (higherDirectImage Λ π q ...)`.
  `higherDirectImage` is the homology in degree `q` of the bounded-below derived
  direct image of the input sheaf placed in degree zero, exactly the node's `R^q`.
  `IsZero` on this abelian category expresses equality to zero up to its unique
  zero-object isomorphism. Degree zero is addressed by the first conjunct.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded category of etale
  sheaves, represented by Mathlib `CategoryTheory.Sheaf` with `ModuleCat Λ` values.
  The corresponding source module available in this clone is
  `lean/Sheaf/AlgebraicGeometry/EtaleSheaves.lean`; the recorded upstream import is
  available to the server compiler. None of its local-constancy predicates is imposed.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`:
  `AlgebraicGeometry.Etale.isIso_etaleLowerShriekBaseChangeMap`. This proof-dependency
  import is public because the signature explicitly uses its proof of invertibility.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`:
  `AlgebraicGeometry.Etale.higherDirectImage` implements the recorded direct-image
  node's derived-cohomology construction.

All recorded, stated proof-dependency modules are also imported. The open-immersion
etale lemma is a Mathlib leaf whose instance is already available. The declaration
docstring carries the five-step proof, including the degree-zero compatibility on
germs that identifies the actual adjunction map.

Edge cases checked: empty open `U` (extension by zero is zero); empty `X` or `Y`
when the isomorphism hypothesis can hold; the zero sheaf; the one-element coefficient
ring; identity proper map; the whole open `U = X` (the isomorphism hypothesis then
forces π to be an isomorphism). No nonemptiness or nonzero-ring assumption excludes
these. Positive integer degrees include every positive natural degree; no assertion
of degree-zero vanishing is made. The usual shared scheme universe and the project's
`u + 1` module-sheaf convention are used with explicitly bound universe `u`.

Searches made:

- `msearch.py`, LeanFinder: “Proper direct image of extension by zero from an
  isomorphism locus has no positive higher direct images”: eight general
  derived-category/homological-complex results, no matching etale-sheaf theorem.
- `msearch.py`, Loogle: `AlgebraicGeometry.Etale.lowerStar, IsIso`: zero hits;
  the public Loogle index does not know the project identifier.
- `msearch.py`, grep: `modification|extensionByZero|proper.*shriek`: 25 unrelated
  Mathlib hits (valuation modification, probability, and tactic implementation).
- `msearch.py`, LeanSearch: “Proper pushforward of extension by zero from an open
  subset over which the map is an isomorphism”: service unavailable, Internal Server
  Error; no result claimed from that service.
- `rg` over the source project's open-immersion directory found the existing
  base-change morphisms and stalk comparisons, not this proper-modification theorem.
  The proper-base-change theorem module has no matching modification or
  extension-by-zero statement.
- `rg` for the item id and `modificationExtensionZero|modification_extension_zero`
  in the source project and `lean/Sheaf` returned no existing declaration; the chosen
  declaration name also has no match in Mathlib or `dag/lean_names_upstream.json`.

Validation: server `scompile.py NX lem-finrepair-modification-extension-zero` compiled
this file cleanly (2.9 seconds for the delivered file), with the mandated nice 19,
two threads, and 60-second per-file limit. The first attempt exposed a private import
of the invertibility theorem used by the signature; making that import public
resolved it. No local compiler or global build was run.

## Second reading by NX

Independently read the sandbox node, its blueprint source at
`sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-modification-extension-zero.md`,
the delivered Lean file, every statement-dependency node and the declarations used
from those nodes. Also read Stacks `etale-cohomology.tex`, labels
`lemma-shriek-base-change` (03S6), `proposition-describe-jshriek` (03S5),
`lemma-stalk-pullback` (03Q1), and `lemma-proper-base-change-stalk` (0DDF).
The first three assume arbitrary schemes; the proper fibre formula requires torsion
coefficients, supplied here by the finite ring. No global Noetherian, separated-base,
characteristic, or invertibility hypothesis is missing. The finite-ring context is
explicit in the reviewed DAG node; the blueprint argument is its proper-fibre argument.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

- Finite commutative ring Lambda: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This does not impose finite stalks or a nonzero ring.
- Schemes X, Y, U: `{Y U X : Scheme.{u}}`. No extra scheme instances occur.
- Proper morphism pi: `(π : Y ⟶ X) [IsProper π]`. Opened Mathlib's class in
  `Morphisms/Proper.lean`: separated, universally closed, locally finite type;
  universal closedness supplies quasi-compactness, hence the node's finite type.
- Open immersion j: `(j : U ⟶ X) [IsOpenImmersion j]`. Opened the recorded
  abbreviation in Mathlib `OpenImmersion.lean`, using locally ringed spaces.
- U' and its projections: `pullback π j`, `pullback.fst π j`, `pullback.snd π j`.
  Opened `HasPullback.lean`: these are the chosen limit and projections with
  codomains Y and U respectively. Scheme pullbacks exist without an added binder.
- Isomorphism h: `[IsIso (pullback.snd π j)]`. This is a substantive hypothesis,
  precisely the projection U' to U, not an isomorphism of the other projection.
- Arbitrary module sheaf G: `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  Read the etale-sheaf dependency's explicit two-encoding note: this is the
  agreed six-functor encoding. No local constancy or constructibility is imposed.
- G' = inverse image along h: `(upperStar (ModuleCat.{u + 1} Λ)
  (pullback.snd π j)).obj G`. Opened `UpperLowerStar/Defs.lean`: `upperStar`
  is the sheafified inverse image, `lowerStar` is evaluation on base changes,
  and `upperStarLowerStarAdjunction` is their specified adjunction.
- Extension by zero F = j'_!G': `openImmersionLowerShriek ... (pullback.fst π j)`
  in the second conjunct. Opened `OpenImmersion/Defs.lean` and `EtaleMap.lean`:
  the open and etale constructions both unfold to sheaf pullback along the same
  `MorphismProperty.Over.map ⊤ h`. Thus the first conjunct's `etaleLowerShriek`
  also denotes the recorded open extension, definitionally, not a substitute.
- Specified canonical map E = j_!G to pi_*F: the inverse natural transformation
  `@inv ... (etaleLowerShriekBaseChangeMap Λ π j)
  (isIso_etaleLowerShriekBaseChangeMap Λ π j)` is evaluated at G and passed
  through `(upperStarLowerStarAdjunction ... π).homEquiv _ _`.
  Opened both side modules: base change is the inverse conjugate of the
  recorded underived exchange, with direction F to pi^-1 E. Its inverse has
  direction pi^-1 E to F, so the hom equivalence gives exactly E to pi_*F.
  `IsIso` is asserted for this actual map. The explicit invertibility proof is
  an imported theorem, not an additional hypothesis.
- Every positive higher direct image is zero: `∀ q : ℤ, 0 < q → IsZero
  (higherDirectImage Λ π q F)`. Opened `SmoothBaseChange/Defs.lean`, lines
  99–106: this is degree-q homology of bounded-below right derived `lowerStar`
  of F in degree zero. `IsZero` applies to a module sheaf object. Integer
  positive degrees express exactly all q > 0 and include every positive natural q.
- Quantification is ring, schemes, maps with their hypotheses, arbitrary G,
  then both conclusions, with q quantified only in the second conclusion.
  There is no existentially chosen map replacing the canonical map.

Edge cases: empty U, X or Y are not excluded; when U is empty both extensions
are zero. The zero sheaf and the one-element ring are allowed. For j an identity
the h-isomorphism hypothesis forces pi to be an isomorphism. Degree zero has
the map-isomorphism conclusion, not a vanishing requirement. There is no index
family or n parameter and no restriction on residue characteristics. Universe u
is explicitly bound; the shared scheme universe and u+1 module universe are the
recorded site convention, with no smaller test universe or vacuous quantifier.

Independent searches used different phrases from the worker:

- `msearch.py ... leanfinder "Proper pushforward of open extension by zero along
  an isomorphism locus vanishes in higher degrees"`: eight homological-complex
  support / derived-category single-object results; none concerns this statement.
- `msearch.py ... loogle "IsIso, CategoryTheory.Adjunction.homEquiv"`: zero hits;
  remote index reports unknown identifier IsIso, so no completeness claimed.
- `rg -i` on Mathlib, upstream WeilConjectures and project `lean/Sheaf`, for
  `modification.*(zero|shriek)`, `proper.*extension.by.zero`,
  `extension.by.zero.*proper`, and `modification_extension_zero`: no exact theorem.
  Opened the related upstream
  `isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring` and
  `isZero_plus_upperStar_lowerStar_openImmersionLowerShriek` declarations.
  They concern exchange on arbitrary derived objects, respectively restriction
  to a closed complement; neither states this canonical underived map together
  with all positive higher-direct-image vanishings. They are useful proof tools,
  not an existing exact declaration to record for this node.

No mismatch found; the module and node signature are retained verbatim. There
are no new definition nodes, dependency modules, or statement corrections to
review. No data definitions or private notions are introduced; the only new
proof is a named public theorem with whole-proof `sorry`. The source-labelled
docstring follows all five DAG proof steps, including compatibility on germs
which identifies the specified map. Public imports expose everything in the
signature. All variables and universes are bound and all lines meet 100 columns.
