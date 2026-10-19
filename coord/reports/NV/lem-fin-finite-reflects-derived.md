## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteReflectsBoundedConstructible` states
`AlgebraicGeometry.Etale.isBoundedConstructible_of_finite_rightDerivedLowerStar`.
Its sole proof is `sorry`; there are no new definitions or other declarations.
The node and its statement dependencies are unchanged except for its `lean` record.

Clause-by-clause correspondence:

- The schemes Z and S and their morphism p are `{Z S : Scheme.{u}}` and `(p : Z ⟶ S)`.
- Noetherian schemes are `[IsNoetherian Z] [IsNoetherian S]`, meaning locally
  Noetherian and quasi-compact, not just topologically Noetherian.
- A finite morphism is `[IsFinite p]`, exactly the recorded affine-local definition.
- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Ordinary derived etale module categories are `DerivedCategoryModule Λ Z` and
  `DerivedCategoryModule Λ S`, the derived categories of
  `Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. The arbitrary object
  `(K : DerivedCategoryModule Λ Z)` has no boundedness or constructibility hypothesis.
- Derived direct image is `(rightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).obj K`.
  This is the upstream total right derived direct image on the unbounded category,
  not `rightDerivedLowerStarPlus`. Its underived functor is the dependency's `lowerStar`.
- Reflection of membership is precisely the implication from `hK`, bounded
  constructibility of that image on S, to `DerivedCategory.isBoundedConstructible Λ Z K`.
  The reused predicate means all cohomology sheaves are constructible and vanish
  outside some interval `[a,b]`, `a ≤ b`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded category vocabulary,
  particularly `AlgebraicGeometry.Etale.DerivedCategoryModule`, originally defined in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, and the Mathlib
  `DerivedCategory.homologyFunctor` used inside the bounded constructibility predicate.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its existing derived extension is
  `AlgebraicGeometry.Etale.rightDerivedLowerStar` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  The old dependency record puts `rightDerivedLowerStarPlus` in Defs, but its actual
  source is UpperLowerStarCoherence; no dependency replacement is necessary because
  the recorded `lowerStar` is fully usable and the unbounded derived extension exists.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.

The private proof-plan imports cover every proof dependency already stated:
`WeilConjectures.SixFunctors.Finite.Exact` (finite exactness and derived comparison),
`Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`),
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (`Functor.mapDerivedCategory`),
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` (`Functor.exactFunctor_derivedFunctor`),
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (`Functor.homologyFunctorIso`),
`WeilConjectures.SixFunctors.Finite.Stalk` (`Etale.lowerStarSheafFiberIsoPi`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
(`Scheme.isIso_of_isIso_sheafFiber_map`). The shared bounded-constructibility definition
is already publicly imported. `lem-fin-finite-reflects-constructibility` has no Lean record
on the read base, so it has no import yet; its proof role is explicit in the docstring.

Edge cases checked before writing: empty source or target schemes; the zero coefficient
ring (no Nontrivial hypothesis); zero complexes; initially unbounded K; finite maps that
are not surjective (each source stalk still occurs over its image); nonreduced schemes;
arbitrary residue characteristics (no coefficient invertibility requirement). No case
requires a source correction. There is no STATEMENT-DISPUTED issue.
The universe convention is the existing etale-module encoding, with schemes in u and
modules and coefficients in u+1; no independent smaller index universe is introduced.

Searches made with `msearch.py NV lem-fin-finite-reflects-derived`:

- `leanfinder "finite morphism derived direct image reflects bounded constructibility
  of etale module complexes"`: eight hits, concerning constructible subsets and etale
  morphism properties, none stating this theorem.
- `loogle "DerivedCategory, IsFinite, lowerStar"`: zero hits; unknown identifier IsFinite.
- `grep 'reflects.*constructible|finite.*direct.*image'`: two irrelevant Mathlib
  AffineSpace/FiniteDimensional hits, no match.
- `leansearch "finite direct image reflects bounded constructibility"`: service
  unavailable, Internal Server Error; not treated as a negative mathematical search.
- Local `rg` on the source WeilConjectures tree and project `lean/Sheaf`, using
  `reflects.*[Cc]onstruct|[Cc]onstruct.*reflect`, the blueprint id, and direct-image
  declaration patterns: found curve-specific sheaf reflection, forward derived
  preservation, and the unbounded derived functor, no existing statement for this node.
- Local search of `dag/lean_names_upstream.json`, project `lean/Sheaf`, and source
  WeilConjectures for the chosen declaration name found no name collision.
- Read the upstream stability direct-image search results: their forward preservation
  theorems and source constructibility predicate do not state this reflection result.

Validation uses only `scompile.py` on the server and `deliver2.py --no-push`.

## Second reading by NV

Independent reading of the unchanged node, its blueprint source at
sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-derived.md, and the delivered
Lean module. The source introduces exactly the following objects, hypotheses and
conclusion; each corresponds to the Lean as follows.

- Objects: schemes Z and S, and their morphism p. Lean has `{Z S : Scheme.{u}}`
  and `(p : Z ⟶ S)`. Verdict: exact. I read Mathlib's Scheme structure and the
  dependency node def-pc-scheme, not just the declaration name.
- Hypotheses: both schemes are Noetherian and p is finite. Lean has
  `[IsNoetherian Z] [IsNoetherian S] [IsFinite p]`. Verdict: exact.
  Mathlib's Noetherian class extends locally Noetherian and compact; IsFinite
  extends IsAffineHom and requires finite ring maps on affine opens, agreeing
  with def-weil-finite-integral-morphism. No field, separation, surjectivity,
  reducedness or coefficient-invertibility assumption is added.
- Coefficients: a finite commutative ring Λ. Lean has `(Λ : Type (u + 1))`
  `[CommRing Λ] [Finite Λ]`. Verdict: exact, including the zero ring. Finite
  does not request chosen enumeration or nontriviality.
- Domain of the reflection assertion: an arbitrary K in the ordinary derived
  category of etale Λ-modules on Z. Lean has `(K : DerivedCategoryModule Λ Z)`.
  Verdict: exact. I opened DerivedCategories and the upstream Coefficients module:
  this abbreviation is DerivedCategory of Sheaf Z.smallEtaleTopology
  (ModuleCat Λ), not Plus, a pro-etale category, or a Tor-finite subcategory.
- Functor: total derived direct image Rp_*. Lean has
  `(rightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).obj K`. Verdict: exact.
  I opened lowerStar in UpperLowerStar.Defs: it is sheaf pushforward along
  etale base change, evaluating G on V ×_S Z. I also opened
  UpperLowerStarCoherence: rightDerivedLowerStar is precisely the unbounded
  rightDerivedFunctor of that lowerStar. The bounded-below declaration in the
  dependency record is not substituted for it.
- Hypothesis and conclusion: if Rp_*K belongs to D^b_c(S), K belongs to D^b_c(Z).
  Lean's hK is DerivedCategory.isBoundedConstructible Λ S of this image, and
  the conclusion is DerivedCategory.isBoundedConstructible Λ Z K.
  Verdict: exact implication for every K, with no converse or extra clause.
  I opened BoundedConstructibleComplexes and IsConstructibleEtaleModuleSheaf:
  the former requires every integer cohomology sheaf constructible and some
  integers a ≤ b bounding its nonzero degrees; the latter uses a finite locally
  closed constructible stratification with etale-local finite constant module
  values. These are the dependency nodes' notions, not the distinct upstream
  finitely-generated-stalk predicate.

Source and proof check: the blueprint source has these same hypotheses, without
an ambient field or invertible exponent. The cited Stacks derived.tex
lemma-right-derived-exact-functor (015F), parts (3)-(4), explicitly treats all
complexes and the unbounded derived category. I read that lemma and homology.tex
lemma-exact-functor (010N); neither introduces a boundedness assumption on K.
The declaration docstring reproduces all three node proof steps: module exactness
and cohomology comparison, stalkwise reflection of zero and hence the same
cohomological bounds, and reflection of constructibility degree by degree with
zero sheaves outside the interval. Its source and blueprint identifiers are
present, as are the module header and proof-plan imports. No definitions, private
copies, local notation or proofs were introduced; the sole theorem proof is sorry.
There are no new nodes, dependency modules, or statement corrections to review.

Edge cases: empty Z gives the zero source category; empty S forces empty Z and
is not excluded. A finite map need not be surjective: a source geometric stalk
still occurs above its own image point, so empty fibres elsewhere cause no
problem. The zero ring, zero complex, and a complex concentrated in degree 0 are
covered; the bounding interval may have a = b = 0. Initially unbounded K is
allowed, with bounds inferred only from hK. All residue characteristics are
allowed, including those dividing the ring order. Universe u is explicit and
arbitrary, with the shared coefficient/module universe u+1; a finite ring can
be represented there and no independently small test universe or index type
makes a hypothesis vacuous. All variables and universes are bound explicitly.

Independent searches used different words from the first reader:

- msearch leanfinder: "cohomology of finite pushforward detects bounded
  constructible complexes" returned eight generic Mathlib t-structure results,
  such as DerivedCategory.isGE_Q_obj_iff, not this reflection theorem.
- msearch loogle: `"rightDerivedLowerStar"` returned zero hits.
- msearch grep: `pushforward.*constructib|constructib.*pushforward|bounded.*faithful`
  returned only an unrelated normed-module bounded-order instance.
- msearch leansearch: "A finite pushforward detects boundedness and
  constructibility of an etale complex" was unavailable (Internal Server Error);
  this is not counted as a negative search result.
- Direct rg over Mathlib, the source WeilConjectures tree, project lean/Sheaf,
  and dag/lean_names_upstream.json used reflection/boundedness/constructibility
  patterns and the proposed declaration name. The closest project result is
  Scheme.isConstructibleSheaf_of_finite_lowerStar_module, whose signature I
  opened: it assumes a curve over an algebraically closed field and concerns
  individual sheaves using the other constructibility predicate. The upstream
  exact-functor result reflects boundedness but has no etale constructibility
  clause. The Finiteness modules preserve constructibility in the forward
  direction under stronger geometric assumptions. None is this statement.

Mismatches found: none. No Lean or node change was needed; only this independent
review was appended. The node's lean.statement was checked verbatim against the
file signature. Server scompile.py compiled the delivered module cleanly
(1.5 seconds, nice 19, two threads, 60-second per-file limit); its required side
imports also compiled individually in the private overlay. No local compiler
or global build was run.
