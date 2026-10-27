## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeDifferentialsSheafUniversalProperty`
states `AlgebraicGeometry.Scheme.Hom.relativeDifferentials_sheaf_universal_property`.
Its only theorem has proof `sorry`. No notion is redefined, no dependency interface is
replaced, and no statement correction is needed.

Hypothesis and clause correspondence:

- A morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`, with no smoothness,
  finiteness, separation, nonemptiness, or field assumption.
- The specified differential sheaf is the recorded `f.relativeDifferentials`;
  its specified derivation is `f.relativeDifferentialsDerivation`. These are the
  upstream constructions, not an arbitrary candidate sheaf or map. Their affine
  interpretation is `relativeDifferentialsSpecIso` and
  `relativeDifferentialsRestrictFromSpecIso`, including the matching derivations.
  The ring differential is the recorded `KaehlerDifferential` with `D`.
- An arbitrary module sheaf is `(M : X.Modules)`. Reading Mathlib's definition gives
  `Scheme.Modules X := SheafOfModules.{u} X.ringCatSheaf`, exactly the general-site
  dependency `CategoryTheory.ringedSiteModules` specialized to this ringed site.
  There is no quasi-coherence assumption on M or on the naturality target N.
- Relative derivations use the existing
  `M.val.Derivation' f.pullbackPresheafToPresheaf`. Its fields `d`, `d_mul`, `d_map`,
  and `d_app` mean additive maps on every open, Leibniz, restriction compatibility,
  and vanishing on the inverse-image presheaf. A compatible family of additive
  maps is a morphism of the underlying sheaves because source and target are
  sheaves. The upstream `derivationMk` and
  `exists_appLE_eq_pullbackPresheafToPresheaf_app` identify this base-vanishing
  condition with the node's condition on sections from arbitrary base opens;
  restricting those sections gives the condition on every W contained in a preimage.
  Thus `relativeDifferentialsDerivation` being typed as such a Derivation' already
  supplies the assertion that d is an S-derivation.
- The first conjunct is `Function.Bijective` of exactly
  `fun α ↦ f.relativeDifferentialsDerivation.postcomp α.val`. This is the specified
  map α ↦ α ∘ d, with no chosen unrelated bijection.
- The second and third conjuncts say this map preserves addition and zero on
  EVERY open W and EVERY section a. This is an unbundled statement of the
  abelian-group isomorphism: derivations are determined by these section maps,
  their canonical group operations are sectionwise, and bijectivity plus these
  identities gives the additive isomorphism, including negatives and its inverse.
  In particular the statement does not choose an arbitrary group structure on
  the set of derivations, or merely assert a bijection while omitting additivity.
  No separate new notion or group instance is necessary to state this property.
- The fourth conjunct quantifies over every module sheaf N, morphism h : M ⟶ N,
  and α. Its equality of derivations is precisely the naturality square for
  postcomposition. The inverse square follows from the asserted bijectivity.
- The fifth conjunct quantifies over every open immersion j : U ⟶ X, and hence
  includes the inclusion of every open subscheme, and all W : U.Opens and
  a : Γ(U,W). The map on Hom is
  `(f.relativeDifferentialsRestrictIso j).inv ≫ (Modules.restrictFunctor j).map α`,
  namely α restricted and composed with the inverse of the canonical differential
  restriction isomorphism. The right side is the restriction of α ∘ d, evaluated
  on a transported through `(j.appIso W).inv`. Its values belong to the same
  sections of M on `j ''ᵁ W` as the restricted module sheaf, by Mathlib's actual
  `restrictFunctor` definition. This is the full forward restriction square.
  Bijectivity applied to U gives compatibility of inverse factorizations too.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`,
  `relativeDifferentialsHomEquiv`, its apply and inverse-section lemmas,
  `relativeDifferentialsRestrictIso`, `relativeDifferentialsToRestrict_app_d`,
  `relativeDifferentialsSpecIso`, `relativeDifferentialsRestrictFromSpecIso`,
  `derivationMk`, and `Scheme.Modules.derivation_ext_of_isAffine`.
  The last is the closed upstream declaration named by the affine-ext dependency's
  lean audit; that dependency's lean record omits module, but its audit supplies it.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  it is the transparent abbreviation for `SheafOfModules` used by `Scheme.Modules`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde.adjunction`
  and `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` (proof dependency).
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`:
  `SheafOfModules.existsUnique_hom_of_cover` (proof dependency).

The recorded statement-dependency modules are public imports; stated proof-only
modules are plain imports. The existing differential module also supplies the
recorded affine-ext proof dependency. The docstring carries all five proof steps:
affine derivation laws, affine factorization, overlap gluing, additivity/naturality,
and the restriction isomorphism and square.

Edge cases checked by reading the quantifiers and canonical constructions:
empty X and the empty open, zero M, identity f and identity j, arbitrary open
immersions including empty U, non-affine and non-quasi-separated X, arbitrary
characteristic, and module sheaves that are not quasi-coherent. There is no affine
intersection assumption. The universe is the same explicit u throughout the
scheme/module interfaces, and no implicit universe or object is auto-bound.

Searches actually run:

1. `msearch.py ... leanfinder` with query "Universal property of the sheaf of
   relative Kahler differentials additive equivalence natural and restriction"
   returned 8 hits, principally presheaf `DifferentialsConstruction.isUniversal'`,
   `relativeDifferentials'`, its section and map lemmas, and `derivation'`, plus
   ring tensor-differential equivalences. None states the scheme theorem with
   additive and open-restriction clauses.
2. `msearch.py ... loogle '"relativeDifferentials"'` returned four presheaf
   construction declarations, not the complete scheme theorem.
3. `msearch.py ... grep 'relativeDifferentialsHomEquiv|Derivation.*AddEquiv|derivation.*[Nn]atural'`
   returned a Lie derivation documentation hit only.
4. `msearch.py ... leansearch` with query "The sheaf of relative differentials
   represents relative derivations naturally and commutes with restriction to
   open subschemes" returned eight hits, mostly presheaf differential construction
   lemmas and scheme restriction definitions, not this theorem.
5. `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
   `relativeDifferentialsHomEquiv|Derivation.*AddEquiv|derivation.*[Nn]atural`
   located the upstream Hom Equiv, its factorization identities and consumers.
   Reading its complete definition shows it supplies the underlying bijection;
   it does not state the additive/natural/restriction conjunction delivered here.
   The upstream postcomposition helper supplies associativity, also not the whole
   statement. Searching the upstream tree for the exact node id returned no match.

Sources read locally: `morphisms.tex`, labels
`lemma-universal-derivation-universal`, `lemma-differentials-restrict-open`,
`lemma-affine-case-derivation`, `lemma-differentials-affine`, and the following
gluing remark. These are Tags 01UR, 01US, 01UO and 01UT, as recorded by the node.
No source-based correction or disputed statement was found.

Validation: `scompile.py Q63 lem-sfb-relative-differentials-sheaf-universal-property`
compiled the initial complete statement in both sandbox and library modes without
errors or warnings (approximately 2 seconds each). Required direct dependency
imports were then completed; the final file is validated again by the delivery
wrapper's per-file compile.

## Second reading by Q63

I made a second pass with the complete JSON statement and the Lean module open;
this is a self-check, with the maintainer's independent delivery review still to
come. The scheme and arbitrary module binders match, and the canonical differential
object and derivation are reused. The derivation type includes all additive,
Leibniz, restriction, and base-vanishing laws. I checked that base vanishing is on
the presheaf inverse image and read the upstream representation lemma and
`derivationMk` to confirm equivalence with the node's every-base-open condition.
I checked the addition and zero identities on every open section, the equality of
postcomposed derivations for naturality, and the direction of the restriction
isomorphism: the inverse must precede the restricted α. The right side uses the
inverse of `j.appIso`, taking a section on U back to its image open in X. The
restricted module sections agree definitionally with that target, as confirmed
by the clean compile. The first bijectivity clause supplies inverse naturality
and inverse restriction compatibility; these are not independent missing clauses.
No hypothesis, conclusion or edge case was removed. No mathematical mismatch
was found. This pass added the explicit direct Mathlib dependency imports and
proof-only Tilde import, without changing the statement.
