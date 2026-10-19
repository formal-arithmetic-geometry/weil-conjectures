## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange` states
`AlgebraicGeometry.Etale.nonempty_iso_etale_open_proper_interchange`, with `sorry`
as its whole proof. It adds no definition and changes no natural-language statement.

Clause-by-clause correspondence:

- Finite commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The universe matches the existing coefficient category `ModuleCat.{u + 1} Λ`
  for schemes in universe `u`; finite rings of any cardinality, including the zero
  ring, are allowed.
- Schemes T, B, V and the two maps: `{T B V : Scheme.{u}} (p : T ⟶ B)
  (i : V ⟶ B)`.
- Properness of p: `[IsProper p]`.
- Quasi-compact open immersion i: `[IsOpenImmersion i] [QuasiCompact i]`.
- The formed fibre product T_V is Mathlib's chosen `pullback p i`;
  b is `pullback.fst p i` and p_V is `pullback.snd p i`.
  Their commutativity and their open/proper properties come from the existing
  pullback condition and base-change instances, rather than extra hypotheses.
- Small etale module sheaves and D+: the source and target of
  `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f` are exactly
  `DerivedCategory.Plus (Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- Derived direct images: `rightDerivedLowerStarPlus` along p_V and p.
- Degreewise extension by zero: `openImmersionLowerShriek ... i` and
  `openImmersionLowerShriek ... (pullback.fst p i)`, each followed by
  `.mapDerivedCategoryPlus`, the bounded-below descent of an exact functor.
- The natural functor isomorphism i_! Rp_V,* ≅ Rp_* b_! is
  `Nonempty (rightDerivedLowerStarPlus ... (pullback.snd p i) ⋙
  (openImmersionLowerShriek ... i).mapDerivedCategoryPlus ≅
  (openImmersionLowerShriek ... (pullback.fst p i)).mapDerivedCategoryPlus ⋙
  rightDerivedLowerStarPlus ... p)`.
  Lean's `⋙` lists application order, so the left side first pushes forward
  to V and then extends to B. `Nonempty` asserts existence of an isomorphism
  of the entire functors, including naturality and inverses, as the node asks.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- The conventions dependency is expressly a collection, not a declaration;
  `IsProper`, `IsOpenImmersion`, and `QuasiCompact` are the corresponding
  Mathlib notions, imported from their owning modules.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, and `pullback.snd`, with the scheme pullback instances.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded etale coefficient
  encoding. Its existing `DerivedCategoryModule` comes from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; D+ is the recorded
  `DerivedCategory.Plus` of the same module-sheaf category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`. The full derived definition is in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`; this module is imported
  publicly to use that exact definition.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, with its exactness instances.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, read with its full signature
  and docstring; available through the public derived-functor import.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `AlgebraicGeometry.Etale.properOpenInterchangeCoherence`, whose full signature
  and proof docstring were read. It is a proof-only import and supplies this
  Cartesian specialization by its existential derived isomorphism family.
- The two Mathlib proof leaves are the open-immersion base-change instances
  in `Mathlib.AlgebraicGeometry.OpenImmersion` and the proper base-change
  instances in `Mathlib.AlgebraicGeometry.Morphisms.Proper`.

Source checked: `literature/stacks-project/more-etale.tex`,
`lemma-shriek-proper-and-open` (Tag 0F7B), statement and proof. Case (b)
allows torsion rings; a finite ring is torsion, so no residue-characteristic
or invertibility condition belongs in the statement. The node's complete
one-step proof plan, including both base-change leaves, is in the docstring.

Edge cases checked before writing: empty V (both functors yield zero), empty
T, identity i (identity extension by zero), identity p (the corresponding
pullback identification), the zero coefficient ring, and finite rings whose
characteristic equals a residue characteristic. No nonempty, nontrivial,
Noetherian, qcqs-scheme, or characteristic condition is introduced. D+ has
arbitrary lower bound rather than only nonnegative complexes.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query "Extension by zero along an open immersion
  commutes with proper derived direct image on small etale sites": eight
  results on scheme module restriction composition and locally ringed-space
  open-immersion maps; no etale derived statement.
- `msearch.py loogle`, query
  "AlgebraicGeometry.Etale.openImmersionLowerShriek,
  AlgebraicGeometry.Etale.rightDerivedLowerStarPlus": no hits, unknown first
  identifier in the Mathlib search index.
- `msearch.py grep`, query `proper.*[Oo]pen|[Oo]pen.*[Pp]roper|[Ss]hriek`
  in AlgebraicGeometry: 25 displayed hits, all unrelated imports or scheme
  open-immersion material, no matching derived interchange.
- `msearch.py leansearch`, query "proper pushforward commutes with extension
  by zero on etale sheaves": service unavailable, Internal Server Error.
- `rg` of `properOpenInterchange|proper.*[Oo]pen.*[Ii]nterchange|[Oo]pen.*[Pp]roper.*[Ii]nterchange`
  in upstream `WeilConjectures` and project `lean/Sheaf`: the stronger recorded
  coherence theorem and references in consumers; upstream
  `OpenImmersionLowerShriekLowerStarExchange` is an unbounded exchange theorem
  with additive torsion hypotheses, not this bounded-below finite-ring statement.
  Its full map and theorem signatures were read; it is not restated here.
- `grep -rn` of this item's id in upstream `WeilConjectures`: no hits.
  `rg` in project `lean/Sheaf` finds proof-plan references in the two consumers,
  not an existing declaration. `dag/lean_names_upstream.json` was also searched
  for the proper/open labels.

No disputed statement, missing notion, dependency repair, or source correction
was found. The quasi-compactness assumption is retained exactly as stated,
although the stronger proof dependency does not need it.

## Second reading by NC

I reread the node `lem-weil-pbc-etale-open-proper-interchange`, its Lean module, all
recorded statement dependencies, and Stacks Project `more-etale.tex`, Tag 0F7B,
`lemma-shriek-proper-and-open`.

The node's objects and hypotheses match the Lean as follows.

- The finite commutative coefficient ring is rendered by
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.  This is the recorded
  `ModuleCat.{u + 1} Λ` encoding and admits the zero ring and every finite
  characteristic.
- The three schemes and maps are
  `{T B V : Scheme.{u}} (p : T ⟶ B) (i : V ⟶ B)`.
- Properness of `p` is exactly `[IsProper p]`; the quasi-compact open immersion
  hypothesis on `i` is exactly `[IsOpenImmersion i] [QuasiCompact i]`.
  No Noetherian, separated, finite-type, nonempty, or characteristic hypothesis
  is added.
- The fibre product `T_V = T ×_B V` is Mathlib's `pullback p i`; its projections
  are `b = pullback.fst p i : T_V ⟶ T` and
  `p_V = pullback.snd p i : T_V ⟶ V`.  The pullback condition gives
  `b ≫ p = p_V ≫ i`, while the open-immersion and proper base-change instances
  supply the properties used by the proof dependency.
- The small-etale coefficient categories and bounded-below derived categories
  are rendered by `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
  `DerivedCategory.Plus` through `rightDerivedLowerStarPlus` and
  `mapDerivedCategoryPlus`.  Extension by zero is precisely
  `openImmersionLowerShriek` followed by that derived-category map.
- The conclusion is the existence of the natural isomorphism
  `i_! R p_{V,*} ≅ R p_* b_!` from
  `D^+((T_V)_et, Λ)` to `D^+(B_et, Λ)`.  Lean renders its composition order as
  `rightDerivedLowerStarPlus ... (pullback.snd p i) ⋙ i_!` and
  `b_! ⋙ rightDerivedLowerStarPlus ... p`; `Nonempty` asserts existence of the
  complete natural isomorphism with both inverse and naturality laws.

The source Tag 0F7B assumes proper vertical maps and separated locally
quasi-finite horizontal maps.  In this node's Cartesian specialization, `i` and
its pullback `b` are open immersions (hence satisfy the horizontal assumptions),
while `p` and its pullback `p_V` are proper.  Case (b) of the source applies
because a finite commutative ring is torsion.  Thus the specialization in the
node and the Lean hypotheses are faithful to the source; the node's explicit
quasi-compactness assumption is retained.

I checked edge cases: empty `V`, empty `T`, identity `i`, identity `p`, the zero
coefficient ring, and coefficient characteristic equal to a residue
characteristic.  The statement remains well-typed and includes each case; no
nonemptiness or invertibility condition is hidden in the binders.  The index and
scheme universes are shared (`Scheme.{u}` and `ModuleCat.{u + 1} Λ`), as required
by the small-etale encoding.

For duplicate-definition and existing-statement searches I used:

- `msearch.py ... leanfinder 'proper open interchange derived etale'`: only
  unrelated etale declarations were returned;
- `msearch.py ... loogle 'openImmersionLowerShriek rightDerivedLowerStarPlus'`:
  no hit (the identifier is outside the Mathlib index);
- `msearch.py ... grep 'proper.*open.*interchange'`: no hit;
- `rg` over `WeilConjectures/`, project `lean/Sheaf/`, Mathlib, and
  `dag/lean_names_upstream.json` for proper/open interchange names: only the
  stronger recorded coherence theorem, its consumers, and the unrelated
  unbounded exchange declaration were found.  None has this node's statement.

I found no mismatch and made no changes to the module or node statement.  The
recorded dependency declarations are used as written, and no new definition or
dependency repair is needed.  The prescribed `scompile.py` invocation completed
with no errors or warnings beyond the allowed `sorry` proof warning.
