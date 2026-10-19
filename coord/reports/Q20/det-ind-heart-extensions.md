## Worker report

The module `Sheaf.Paper.IndConstructibleExtensions` states extension closure of the
ambient ind-constructible module sheaves on every Noetherian scheme. Its two declarations
are `AlgebraicGeometry.ProEtale.indConstructible_of_shortExact` (finite E) and
`AlgebraicGeometry.ProEtale.indConstructible_of_shortExact_padicAlgCl` (condensed algebraic
closure). Both proofs are `sorry`; there are no new definitions or helper theorems.
The item changes only in `lean`. Its statement and dependencies are unchanged.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| X a scheme | `(X : Scheme.{u})` |
| X locally Noetherian | `[IsLocallyNoetherian X]`, the recorded Mathlib class |
| X quasi-compact | `[CompactSpace X]`, with no Hausdorff assumption |
| prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| an algebraic closure of Q_ell with the extending absolute value | The existing `PadicAlgCl ℓ` framework fixes this representative, including its norm and topology, throughout the condensed coefficient construction. |
| finite intermediate extension E/Q_ell | `(E : PadicAlgCl.FiniteIntermediateField ℓ)` in the first declaration; the subtype bundles `FiniteDimensional` for an intermediate field of `PadicAlgCl ℓ`. |
| Lambda = underlined E | `Profinite.continuousMapRingObj E`, with E's inherited norm topology |
| Lambda = underlined Qbar_ell | `Profinite.padicAlgClRingObj ℓ` in the second declaration; this is finite-subextension-valued continuous functions, not all continuous functions into the valuation-topological algebraic closure. |
| Lambda_X = p_X^* Lambda | `condensedRingObj ... X`, the unbundled version of the recorded `coefficientRing` using exactly `upperStarFromPoint X` and its transported monoid structure |
| ambient category A = internal Lambda_X-modules in abelian sheaves | `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj ... X)` |
| Cons uses the recorded constructible-sheaf notion | `IsConstantModelConstructible ... X` from `Sheaf.Paper.CondensedConstantConstructibility`; no replacement by the older arbitrary local finite-presentation predicate |
| IndCons consists of objects isomorphic to small filtered colimits in A of Cons | `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible ... X)`; its definition quantifies over small filtered J and a `ColimitPresentation J` of the actual object. Such presentations already absorb isomorphisms, as its `IsClosedUnderIsomorphisms` instance confirms. |
| diagrams small in the fixed site/coefficient universe | The `u + 1` parameter of `ObjectProperty.ind` makes J and its homs small at the universe of the coefficient values and an essentially small model of the site. This matches the sibling filtered-colimits statement. |
| 0 → N → M → B → 0 | `(S : ShortComplex A)` and `(hS : S.ShortExact)`; N, M, B are respectively `S.X₁`, `S.X₂`, `S.X₃`. S includes the compositional-zero condition; `ShortExact` includes middle exactness, monicity and epicity. No particular zero objects or arbitrary linear maps are substituted. |
| N and B belong to IndCons | `hN` and `hB`, using the ind predicate at `S.X₁` and `S.X₃` |
| M belongs to IndCons | The same predicate at `S.X₂`, the conclusion of each theorem |

The two coefficient declarations together cover exactly the disjunction in the node.
The algebraic-closure case does not need an unused E parameter: fixing any finite E
in that case has no influence on the category or conclusion. No base field,
positive-characteristic, separatedness, finite-type or invertibility-of-ell assumption
is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through the scheme imports).
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`:
  `Profinite.continuousMapRingSheaf`, `Profinite.continuousMapRingObj`, and the
  commutative-ring-object instance. The coefficient nodes have closed upstream audit
  bindings, which the standing brief authorizes using directly.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`, and the explicit
  finite-subextension-valued section construction; also read the finite-field condensed
  coefficient construction.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`:
  the normed finite intermediate fields and coefficient inclusions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `upperStarFromPoint`, `condensedRingObj`,
  and its commutative instance. Read from the shared framework specified in the brief.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.ModObj`, `Mod`, and module
  morphisms, using the dependency's closed upstream audit bindings.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, including its
  `HasFiniteConstantLocalModel` and `IsFiniteConstantStratified` constituents and
  `ConstantModelConstructible` full subcategory.
- `Mathlib.CategoryTheory.Limits.HasLimits` and
  `Mathlib.CategoryTheory.Filtered.Basic`: cocones, `IsColimit`, colimits and `IsFiltered`;
  `Mathlib.CategoryTheory.ObjectProperty.Ind`: `ObjectProperty.ind`, its isomorphism
  invariance and `ind_ind`. These implement the existing colimit dependency.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ShortComplex.ShortExact`,
  the exact-sequence dependency's recorded categorical short exact notion.

All stated proof dependencies have ordinary, non-public imports: `SheafTensor`,
`GrothendieckAbelian.Sheaf`, `Monoidal.Mod.Abelian`, the Mathlib Grothendieck and
abelian-category definitions, upstream `PushoutShortExactSequence`,
`YonedaDerivedExtComparison`, Mathlib short five lemma, and
`IndConstructibleFilteredColimits`. The two direct proof dependencies without a Lean
record or Mathlib match (`sk-lem-constructible-ext-continuity` and
`det-lem-coefficient-heart-closure`) do not generate fictitious imports. Each theorem's docstring reproduces all eight steps
of the supplied proof, including the small undercategory and explicit pushout-colimit
universal property.

Edge cases checked before writing:

- The empty scheme is allowed: the statement imposes only local Noetherianity and
  compactness, both compatible with emptiness. No chosen point or nonempty scheme
  is required.
- Zero modules and split short exact sequences remain included. The theorem takes
  every short exact S, including those with zero endpoints or all objects zero.
- Filtered presentations are nonempty by Mathlib's `IsFiltered`, as required by the
  source's definition. No bound on the number of objects or a directed-poset-only
  restriction is imposed.
- Every prime ell is allowed, including 2, and the base scheme may have characteristic
  ell or mixed characteristic. No extra characteristic condition appears.
- E = Q_ell is included as the bottom finite intermediate field. The Qbar case uses
  the source's finite-subextension-valued condensed ring, preserving its crucial
  distinction from the full continuous-function sheaf.
- The ambient colimits remain in the internal-module category, rather than in the
  abstract Ind category or the full constructible subcategory.

Searches made on 2026-10-18:

1. `msearch.py` leanfinder: `Extensions of ind constructible pro etale sheaves are ind constructible`.
   Eight hits: `Condensed.lanSheafProfinite`, `LightProfinite.hasSheafify`,
   `AlgebraicGeometry.Scheme.smallEtaleTopology`, `AlgebraicGeometry.Scheme.etaleTopology`,
   `LightProfinite.hasSheafify_type`, `LightCondensed.ofSheafLightProfinite`,
   `Condensed.ofSheafForgetProfinite`, and `Condensed.lanCondensedSet`. None states
   the extension-closure theorem.
2. `msearch.py` loogle:
   `CategoryTheory.ObjectProperty.ind, CategoryTheory.ShortComplex.ShortExact`.
   Zero hits.
3. `msearch.py` grep: `indConstructible|IndConstructible|IsClosedUnderExtensions`
   in `CategoryTheory`. Six hits in ObjectProperty/Extensions and Abelian/SerreClass/Basic:
   the generic extension-closure definition and its generic consequences, with no result
   about ind-constructible sheaves.
4. `rg -n 'indConstructible|IndConstructible|ind-constructible|det-ind-heart-extensions'`
   over the upstream WeilConjectures source and the side `lean/Sheaf` tree.
   Only the sibling `Sheaf.Paper.IndConstructibleFilteredColimits` was found; it states
   filtered-colimit and sum closure, not extension closure. No exact existing theorem.
5. Read Mathlib `ObjectProperty/Ind.lean`: its ind predicate and isomorphism instance
   match the inline IndCons definition; no second definition is needed.

Node/proof-route issue for the independent reviewer: the item is stated for every
Noetherian scheme, but its recorded proof dependency `det-ind-heart-filtered-colimits`
now has a narrower separated finite-type, positive-characteristic setting. This does
not change the item's statement or require another statement binder. For the needed
Noetherian version of the last proof step, the already cited field-coefficient
Ext-continuity theorem in degree zero says that constructible objects are finitely
presentable. Mathlib `ObjectProperty.ind_ind` then flattens the ind-of-ind presentation,
proving the needed closure without imposing the sibling's extra geometric hypotheses.
This justification is included in both docstrings. The unproved Ext-continuity and
constructible-heart-closure nodes remain legitimate proof dependencies for stage 3.
No statement is marked disputed and no source-based statement correction is needed.

Validation: `scompile.py Q20 det-ind-heart-extensions` compiled the module under its
sandbox and final library module paths, including the side-only sibling overlay.
There were no errors or warnings. All variables and the universe are explicitly bound;
`autoImplicit` is false. The only postponed proofs are the two named item theorems.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
