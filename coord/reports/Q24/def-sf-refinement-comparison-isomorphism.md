## Worker report

The main module defines the objectwise comparison along a refinement. It has real data:
`refinementProperOpenIso` is exactly part (a), and `refinementComparisonAtWitness` is exactly
part (b). The final `refinementComparisonIsomorphism` supplies every geometric and
positive finite-coefficient hypothesis of the node. No statement correction is made.

Hypotheses and clauses:

- `K₀ : Type u`, `[Field K₀]` is the base field. The two `Scheme.Over` instances and the
  `LocallyOfFiniteType`/`QuasiCompact` instances on their structure maps say that X and Y
  are finite-type K₀-schemes. `f.IsOver` says that f is a K₀-morphism; `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f` say separated finite type.
- `l`, `Fact l.Prime`, and `_hl : IsUnit (l : K₀)` give the prime and invertibility.
  `E`, `Field E`, `Algebra ℚ_[l] E`, and `FiniteDimensional ℚ_[l] E` give its finite
  extension. `n : ℕ`, `hn : 1 ≤ n` give the positive integer. The exact coefficient
  ring is the recorded `Padic.coefficientExtensionRing l E n`, lifted by `ULift` into
  the site coefficient universe, with the discrete topology explicitly specified.
  Finiteness uses `Padic.finite_coefficientExtensionRing`.
- `c₁ c₂ : Compactification f` give the actual ambients, open immersions and proper
  structure maps. `r : c₁.Refinement c₂` is the recorded refinement, with `r.hom_g`
  expressing the equation over Y and `r.i_hom` the equation on X. Its properness is
  the existing `Compactification.Refinement.isProper` instance. No Cartesian condition
  and no density condition is added. Finite type over the field implies the stated
  Noetherianity; the canonical maps actually exist without needing that restriction.
- The input `RefinementFiniteLevelOrigin ... X` is the recorded
  `EtaleOriginDerivedCategory X Λ`. Its sigma components are the bounded-below K and
  the retained `EtaleOriginWitness`, hence the bounded-below L and alpha. Morphisms
  remain all ambient morphisms, exactly as in the recorded category.
- The witness category and the recorded compact-support candidate use two coefficient
  presentations. `refinementCoefficientEquivalence` derives the canonical realization
  equivalence, and `refinementFixedObject` is its inverse on K. Thus the output is the
  candidate evaluated on the same K in its fixed-module-sheaf presentation, not on a
  substituted etale-origin complex. `refinementFixedWitnessIso` transports the actual
  retained alpha using the equivalence unit, exact-functor compositor, and bounded-below
  inclusion compositor. All these maps are existing canonical constructions.
- For (a), `properOpenProEtaleIso ... O.2.L` is the canonical proper-open map on the
  etale-origin complex. `refinementProperOpenIso` first applies j₂! to the inverse of
  the transported alpha, then this proper-open map, then Ru_* j₁! to alpha. This is
  precisely the displayed conjugation in the node (Lean composes from left to right).
  For an identity witness this is the same proper-open map under the canonical
  coefficient-presentation identifications; no witness is discarded or replaced.
- For (b), `eqToIso (congrArg ... r.hom_g.symm)` supplies the equality of the ambient
  structural maps; `finiteDirectImageComposition` is c at j₁!K, oriented from the
  composite pushforward to successive pushforwards. The last factor is the proper
  ambient pushforward of the inverse of part (a). Endpoints are explicitly the
  recorded `rightDerivedLowerShriekOfCompactification` values. The result is an `Iso`
  in the ambient unbounded derived category, so no separate arbitrary invertibility
  witness is supplied.
- The main definition claims no naturality, witness independence, identity-refinement
  law or refinement-composition law. The separate proper-open dependency retains its
  own identity/composition assertions, as that dependency requires.

Dependency declarations read and used:

- `WeilConjectures.Compactification.Refinement`: `Compactification`,
  `Compactification.Refinement`, `hom_g`, `i_hom`, and its properness instance.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its construction module:
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.EtaleOriginDerivedCategory`: `EtaleOriginDerivedCategory`; its imported
  `Sheaf.Paper.EtaleOriginWitness`: `EtaleOriginWitness.L`, `.alpha`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientDerivedCategory`,
  its Plus version, `finiteCoefficientRealization`, `finiteCoefficientComparison`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, literally Dj! followed by Rf*.
- The recorded extension-by-zero notion is `ProEtale.openImmersionLowerShriek`;
  here it is imported through the upstream derived lower-shriek module, avoiding the
  duplicate finite-coefficient module that declares the same constants.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the recorded etale derived category
  and site comparison; Mathlib `DerivedCategory.Plus.ι` and the exact-functor comparison
  APIs give the bounded-below inclusions used explicitly.
- `Sheaf.Paper.SfDerivedDirectImage` and
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` were read, including
  their full finite direct-image signatures. Their broader imports introduce the
  duplicate finite-coefficient functor declarations when combined with the recorded
  fixed-scalar candidate. The finite functor used here is the existing upstream
  `lowerStar.rightDerivedFunctor`, the same ordinary K-injective construction. No
  completed or integral direct image is used. The new compositor specializes that
  canonical finite construction; unrelated integral stages are not prerequisites for
  this definition. The realization interface repair avoids the conflicting imports.

Edge cases checked: n = 1 is retained; n = 0 is excluded exactly as in the node.
Empty source/ambient schemes and the zero complex are allowed by all constructions.
All maps are functor maps and isomorphism composites, so no nonzero object is assumed.
Identity refinements are allowed. The formula permits extra components in the inverse
image of the open, unlike the existing etale refinement API requiring a Cartesian square.
The site object/morphism universes are the recorded small pro-etale universes, with the
larger module coefficient universe; no equality of those universes is imposed.

Searches made:

- LeanFinder, query “comparison isomorphism between compact support direct images along
  a proper refinement of compactifications”: eight hits, all topological compact-support
  maps, none a scheme compactification comparison.
- Loogle, query `CategoryTheory.Functor.mapIso, CategoryTheory.Iso.trans`: twelve hits;
  `Functor.mapIso_trans` and generic categorical isomorphism lemmas are ingredients only.
- LeanSearch, query “canonical comparison for derived pushforward of extension by zero
  along proper refinement”: service unavailable, Internal Server Error.
- msearch grep, `refinement.*[Cc]omparison|properOpen|proper_open`, both CategoryTheory
  and AlgebraicGeometry: zero Mathlib hits.
- rg of the upstream source and lean/Sheaf for the item id, candidate, retained-witness
  declarations, proper-open maps, and refinement comparison names found the existing
  etale comparison. Its full signature requires `IsPullback` and has the opposite
  direction and site, so it is not this definition. No existing pro-etale objectwise
  refinement comparison was found. Also checked the upstream declaration-name map.
- The server source and delivery branches were checked for the two missing comparison
  nodes. They have no landed Lean record. The N1 proper-open delivery and N0 coherence
  delivery are stage-1 DAG changes, with no Lean module to reuse. The raw blueprint
  compactification-coherence source and composition source were read on the server.

No STATEMENT-DISPUTED flag or own-statement fault was found.

## Dependency modules

`lem-weil-derived-direct-image-composition`: no recorded Lean interface existed. The
module exposes the finite-level clause (1) consumed here by specializing the existing
unbounded right-derived compositor, whose universal-property normalization is canonical.
Its data is fully constructed from exact inverse image and the actual underived
fibre-product-pasting identification. The other coefficient stages of that node are
not invoked or replaced by this finite-level definition.

`lem-weil-pbc-proper-open-comparison-proetale`: no recorded Lean interface existed.
The module defines the canonical site-extension comparison, the proper-open map on
D+ and its ambient unbounded version. It states the dependency's identity/composition
laws with sorry and the complete transport/cancellation proof plans. The construction
uses the specified etale proper-open map and the canonical direct-image mate, not the
upstream unspecified Nonempty isomorphism. It needs no Cartesian refinement hypothesis.

`def-weil-pbc-proetale-modules`: its recorded intrinsic-comparison interface imports a
second copy of the upstream fixed-coefficient functors. This produces an actual
“environment already contains” error when imported with the recorded compact-support
candidate. The new module imports the smaller original finite-module definitions and
exposes their realization as full, faithful and essentially surjective, giving the
canonical realization equivalence without that conflicting import. Its named theorem
has the module-sheafification proof plan; its instance contains only the theorem's
three structure fields. The coefficient sheaf, module category, comparison inverse
image and bounded-below category are all the original recorded definitions.

## Second reading by Q24

I opened the item node, its source description, every copied dependency node, and all four
Lean files. The node's objects and the corresponding Lean are as follows.

- The base field (K_0), schemes (X,Y), and separated finite-type morphism (f) are
  rendered by `K₀ : Type u`, `[Field K₀]`, the two `X.Over`/`Y.Over` instances, the
  locally-finite-type and quasi-compact structure-map instances, `f : X ⟶ Y`,
  `[f.IsOver ...]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
  `[QuasiCompact f]`. This is exactly the node's finite-type-over-(K_0) and separated
  finite-type hypotheses.
- The prime, invertibility, finite extension, and positive coefficient level are rendered
  by `l`, `[Fact l.Prime]`, `_hl : IsUnit (l : K₀)`, `E : Type u` with `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, `n : ℕ`, and `hn : 1 ≤ n`.
  The coefficient object is exactly `ULift (Padic.coefficientExtensionRing l E n)`;
  `Padic.finite_coefficientExtensionRing` supplies finiteness and the local instances
  supply its discrete topology.
- The compactifications (c_1,c_2) and refinement (u) are rendered by implicit
  `{c₁ c₂ : Compactification f}` and `r : c₁.Refinement c₂`. Their open immersions,
  proper structure maps, `r.i_hom`, `r.hom_g`, and properness instance are the recorded
  `Compactification`/`Refinement` fields and instance; no Cartesian or density
  hypothesis is added.
- The node's retained object `(K,L,alpha)` in the bounded-below etale-origin category is
  rendered by `O : RefinementFiniteLevelOrigin l E n hn X`. Its sigma components are the
  bounded-below pro-etale object and `EtaleOriginWitness`, whose fields `.L` and `.alpha`
  are precisely (L) and \\(\\alpha:\\nu_X^*L\\xrightarrow{\\sim}K\\). The finite-coefficient
  category is the project's canonical encoding of the node's (D^+) categories, and the
  realization equivalence transports it to the fixed-module-sheaf presentation used by
  the recorded compact-support functor.
- Part (a) is rendered by `refinementProperOpenIso`: it maps the inverse transported
  witness to `nu^* L`, applies `properOpenProEtaleIso` to the actual retained `L`, and
  maps the witness forward again. Its source and target are exactly
  `j₂!K ≅ Ru_* j₁!K`, with the Lean composition order matching the displayed
  `Ru_*j₁!(alpha) ∘ alpha_u(L) ∘ j₂!(alpha)⁻¹`.
- Part (b) is rendered by `refinementComparisonAtWitness`: `eqToIso` uses
  `r.hom_g` to identify `c₁.g` with `r.hom ≫ c₂.g`; `finiteDirectImageComposition`
  gives the canonical finite-level compositor; and the image under `Rc₂.g` of the
  inverse of part (a) gives the final factor. The result has exactly the two
  `rightDerivedLowerShriekOfCompactification` endpoints and is an `Iso` in the ambient
  derived category.
- The final node definition `refinementComparisonIsomorphism` specializes all of this to
  the positive finite coefficient ring and returns exactly the node's comparison
  isomorphism. It asserts no naturality, witness independence, identity law, or
  composition law, matching the node's explicit scope statement.

Edge cases were checked: `n = 1` is admitted and `n = 0` is excluded by `hn`; the zero
complex, empty schemes, and identity refinement are admitted; no nonzero-object or
nonempty-index assumption occurs; the prime characteristic is handled only by the stated
invertibility hypothesis; and the site/coefficient universes are the recorded small-site
universes with the coefficient `ULift`, without imposing an equality of independent site
universes. The compactification and refinement structures also admit extra components in
an inverse image of the open.

For the one-definition check I searched the source and project with `rg` for the item id,
`refinement.*comparison`, `properOpen`, and `proper_open`, inspected the upstream
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison` and
Mathlib's derived-functor composition APIs, and ran the recorded LeanFinder, Loogle, and
msearch searches. The upstream comparison is etale-site, requires a Cartesian square, and
has the opposite direction, so it is not this notion. No Mathlib or project declaration
states this pro-etale objectwise comparison.

I found no mismatch between the node and the item definition. The only potentially easy
confusion is that `O` uses the retained finite-coefficient origin category while the
candidate uses fixed scalar module sheaves; the supplied `finiteCoefficientRealization`
equivalence is the canonical presentation change already required by the dependency node,
so this does not add a hypothesis or change the object. The dependency modules likewise
state their copied node notions: the finite compositor is finite-level only, the proper-open
map has the node's hypotheses and direction, and the realization repair supplies the
canonical full/faithful/essentially-surjective interface without an arbitrary choice.
No source-based correction or statement change was needed.
