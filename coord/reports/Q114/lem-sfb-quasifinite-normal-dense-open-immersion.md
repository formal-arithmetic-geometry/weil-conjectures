## Worker report

The module `Sheaf.AlgebraicGeometry.QuasifiniteNormalDenseOpenImmersion` states
`AlgebraicGeometry.isOpenImmersion_of_mono_dense_open_isIso`, with its entire proof
postponed by `sorry`. No definition is introduced and no statement is changed.
The declaration docstring reproduces all seven steps of the accepted proof plan.

Hypothesis and conclusion correspondence:

- Schemes and the given morphism: `{X Z : Scheme.{u}} (f : X ⟶ Z)`.
  The universe `u` is explicitly declared and `autoImplicit` is false.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the two
  properties recorded by `def-weil-finite-type-morphism`.
- Noetherian target: `[IsLocallyNoetherian Z] [CompactSpace Z]`, precisely the
  stated locally Noetherian and quasi-compact conditions. Mathlib's bundled
  `IsNoetherian` extends these same two classes (Noetherian.lean:280).
- Normal target: `hnormal : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
  IsIntegrallyClosed (Z.presheaf.stalk z)`. Both domain and integral-closure
  conditions are retained; this is the recorded normal-domain form, without
  imposing irreducibility or selecting a fraction field separately.
- Reduced source: `[IsReduced X]`. Properties.lean:74--84 identifies the
  sectionwise class with the local-ring condition in the node.
- Monomorphism: `[Mono f]`, categorical cancellation against every scheme
  morphism, equivalently injectivity on `Hom(T, -)` for all schemes `T`.
  This is a categorical monomorphism, not just injection on points.
- Existence of an open subscheme: `hdense : ∃ H : Z.Opens, ...`.
  `Scheme.Opens.toScheme` gives its canonical open subscheme structure.
- Density in the target: the first conjunct `Dense (H : Set Z)`.
- Density of the inverse image in the whole source: the second conjunct
  `Dense (f ⁻¹ᵁ H : Set X)`. This is not density only within that inverse image.
- The specified restriction is an isomorphism: the third conjunct
  `IsIso (f ∣_ H)`. Here `morphismRestrict f H` is the canonical morphism
  `(f ⁻¹ᵁ H).toScheme ⟶ H.toScheme`, defined in Restrict.lean:569--573,
  using the open-subscheme pullback. No unrelated isomorphism is substituted.
- Conclusion: `IsOpenImmersion f`. There are no flatness, irreducibility,
  properness, nonemptiness or finite-presentation assumptions.

Statement dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed` on each
  stalk, following the recorded normal-domain conjunction. The latter is from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and is integral closure
  in `FractionRing` (lines 63--74); no second normality predicate is needed.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`, from
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, from
  `Mathlib.AlgebraicGeometry.OpenImmersion`.

Proof dependency modules are imported without `public`, except where they
already supply a notion in the signature. These are
`Sheaf.AlgebraicGeometry.RegularNormalDecomposition`
(`regular_normal_and_normal_decomposition`, clause 2),
`Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.isBasis_affineOpens` and
`Scheme.compactSpace_of_isAffine`),
`Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite`
(`Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp`),
`WeilConjectures.AlgebraicGeometry.UnramifiedFibrePointIsolated`
(`unramified_fibre_point_isolated`),
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`
(`Scheme.Hom.IsQuasiFinite` and the recorded pointwise/local predicates),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
(`quasiSeparatedSpace_of_isAffine`),
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
(the open-immersion instance for `f.toNormalization`),
`Mathlib.AlgebraicGeometry.Normalization`
(`normalization`, `toNormalization`, `fromNormalization`, their factorization,
normalization charts, integral/dominant instances and integral-source instance),
`Mathlib.AlgebraicGeometry.Properties` (scheme sobriety and `IsIntegral`),
`Mathlib.AlgebraicGeometry.FunctionField`
(`functionField_isFractionRing_of_isAffineOpen`), and
`Sheaf.AlgebraicGeometry.IntegralBirationalNormalIsomorphism`
(`isIso_of_integral_birational_normal`).

Sources read: Stacks more-morphisms.tex, lemma-quasi-finite-separated-quasi-affine
(Tag 02LR), and morphisms.tex, lemma-monomorphism-loc-finite-type-loc-quasi-finite
(Tag 0CT8) and lemma-finite-birational-over-normal (Tag 0AB1, explicitly including
integral morphisms). These give exactly the accepted proof's normalization route.
The current blueprint unit `sk-thm-sf-ctf-stability/_section.md` is a six-functor
statement; this item is its below-unit scheme-theoretic tool, not a unit target.

Edge cases checked before writing:

- If `Z` is empty, any `f` forces `X` empty. Normality is vacuous, and the
  existential permits the empty dense open. No nonempty instance excludes it.
- If `H` is empty, its density forces `Z` empty, reducing to the previous case.
- If `H = ⊤`, its inverse image is all of `X`; the restriction condition says
  that the original morphism is an isomorphism up to the canonical top-open
  identifications, and the open-immersion conclusion is appropriate.
- A disconnected normal Noetherian target is allowed. The source density is
  imposed globally; the proof restricts it to every inverse-image affine open,
  and the target density meets every nonempty component.
- A strict dense open inclusion into a normal Noetherian target satisfies the
  statement, so neither surjectivity nor an isomorphism conclusion is imposed.
- Source density is substantive: for `Z = A¹_k`, let `H = A¹_k \ {0}` and
  `X = H ⊔ Spec k`, with the second component mapping to 0. This finite-type
  monomorphism has reduced source and is an isomorphism over dense `H`, but is
  not an open immersion. Its inverse image of `H` misses the extra component
  and fails exactly the source-density conjunct retained in the Lean statement.

Searches for an existing statement (all through `msearch.py` with this group
and item unless a local source search is indicated):

- LeanFinder: “A finite type birational monomorphism from a reduced scheme to
  a normal Noetherian scheme is an open immersion”. Eight hits: definitions,
  open immersions into relative normalization, the flat-monomorphism theorem,
  and local criteria. None states this normal-target dense-open criterion.
- Loogle: `"IsOpenImmersion", "normal"`. Two hits: open immersion into relative
  normalization, including its quasi-finite-locus variant. Both still require
  the separate identification of that normalization with the normal target.
- Grep: `birational|isOpenImmersion.*[Nn]ormal|[Nn]ormal.*isOpenImmersion`
  in Mathlib/AlgebraicGeometry. Twelve hits on birationality modules and
  normalization; none is an exact match.
- LeanSearch: “A finite type monomorphism from a reduced scheme to a normal
  Noetherian scheme which is an isomorphism over a dense open whose inverse
  image is dense is an open immersion”. Eight hits on general immersion facts,
  monicity of open immersions and the stalk-isomorphism criterion; no match.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for birationality,
  normal open-immersion criteria, dense-open criteria and this node's id.
  The nearby finite/integral birational isomorphism statements are the proof
  inputs already listed, not the requested theorem. No node-id hit upstream.
- Local `rg` in `dag/lean_names_upstream.json` and both source trees for
  `isOpenImmersion_of_mono_dense_open_isIso` and variants combining monicity,
  birationality, density and normality found no declaration with this statement
  or a conflicting declaration name.

All notions have usable existing declarations. No new nodes, dependency
repairs, statement corrections or disputed statements are needed. Validation:
server compilation via `scompile.py`, then `deliver2.py --no-push` and delivery.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
