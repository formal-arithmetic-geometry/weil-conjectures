## Worker report

The module `Sheaf.Paper.ContinuousCoefficientFreeRank` states
`AlgebraicGeometry.ProEtale.continuous_coefficient_finiteFree_rank`, with its whole
proof `sorry`. It introduces no definitions, helper theorems, new nodes, or
replacement dependency interfaces. The node changes only in `lean`.

Source read: Hemo--Richarz--Scholbach, *Constructible sheaves on schemes*,
arXiv:2305.18131, Example 3.1, printed p. 6 (local PDF, page 6). It identifies
pulled-back continuous coefficients on any scheme with `U ↦ C(|U|, E)`.
Also read the first paragraph of the current blueprint
`sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice-rank.proof.md`:
transition isomorphisms on overlaps preserve finite free rank. The statement is the
extracted invariant-rank lemma, not a restriction to the quasi-compact schemes that
occur later in that parent proof.

Every hypothesis and clause is rendered as follows:

- A prime ℓ: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A finite field extension of ℚ_ℓ: `(E : Type u) [NormedField E]`
  `[NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`. `NormedField` supplies
  the field and topology. `NormedAlgebra` supplies the field algebra and compatibility
  with the ℓ-adic norm. This is the specified ℓ-adic topology, not an arbitrary
  topological field: `NormedAlgebra.norm_eq_spectralNorm` identifies this norm
  with the unique extended spectral norm for a finite extension. Conversely the
  canonical spectral norm equips every finite extension with this structure, so
  this encoding adds no hypothesis to the mathematical statement. No completeness
  or separate total-disconnectedness assumption is requested.
- An arbitrary scheme: `(W : Scheme.{u})`, with no other geometric instance.
- The small pro-etale site: the target of `condensedRingObj ... W` is precisely
  `Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}`. The object universe of
  the site is `u+1` and its morphism universe is `u`; neither is collapsed.
- Continuous condensed coefficients `underline E(S) = C(S,E)`:
  `Profinite.continuousCoefficientRingObj E`, publicly available through the
  dependency `Sheaf.Topology.ProfiniteCondensedRing`. Its sections are
  `ULift C(S,E)` with pointwise operations and precomposition; the lift only
  implements the sheaf value universe.
- The actual pulled-back coefficient ring `E_W = p_W^* underline E`:
  `condensedRingObj (Profinite.continuousCoefficientRingObj E) W`. This recorded
  dependency declaration is `(upperStarFromPoint W).obj ...` with the canonical
  transported ring-object structure. It is also the underlying object of the
  recorded bundled `coefficientRing` applied to `Mon.mk` of these coefficients.
  `open scoped CategoryTheory.Obj` enables the library's transported monoid-object
  instance; no local instance or independently chosen ring structure is supplied.
- Natural ranks: `(m n : ℕ)`.
- The direct sums of regular module sheaves: `Mod.finiteFree (...) m` and
  `Mod.finiteFree (...) n`. The upstream definition is literally the finite
  biproduct of `Mod.regular` indexed by `Fin m` and `Fin n`. The empty biproduct
  at rank zero is the zero module, so there is no positive-rank restriction.
- An isomorphism of module sheaves: the binder `_e : ... ≅ ...` is in the bundled
  category `CategoryTheory.Mod` of module objects over this very ring object;
  its morphisms are action-compatible sheaf morphisms, not arbitrary abelian maps.
- Nonempty underlying scheme: `[Nonempty W]`, where Scheme's coercion to a type
  is its underlying space. It does not require connectedness or a chosen point.
- Conclusion: `m = n`, with neither direction omitted.
- The final absence-of-finiteness clause is respected: no quasi-compactness,
  connectedness, Noetherianity, separatedness, base scheme, characteristic
  restriction, or invertibility of ℓ on W occurs anywhere in the signature.

Dependency declarations and signatures/docstrings inspected:

- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`; its public import
  `Sheaf.NumberTheory.Padics.CoefficientExtension` gives
  `Padic.coefficientExtensionAbsoluteValue` and
  `Padic.coefficientExtensionDegree`. The finite-dimensional ℚ_ℓ extension is the
  same input as that API, and the above normed-algebra presentation specifies
  its unique norm. No coefficient finite-level ring is needed in the statement.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` (extends `LocallyRingedSpace` with local affinity).
- `sk-def-pe-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology` from its
  `mathlib_match`; there is intentionally no separate `lean` record.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`, and the publicly retained continuous construction
  `Profinite.continuousCoefficientRingObj` in
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, and its commutativity instance. Their full definitions
  transport the monoid along the strong monoidal inverse image from the point.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`, `Mod.regular`; also
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`, `Mod.finiteFree`, whose
  exact finite-biproduct definition supplies the finite sums in the node.

The module also imports the stated proof plan:
`Sheaf.Paper.ContinuousRingUniverseRealization`,
`AlgebraicGeometry.ProEtale.ContinuousRingUniverse.comparison_isIso` and
`comparison_isMonHom`; `Mathlib.LinearAlgebra.Dimension.Finite`,
`LinearIndependent.fintype_card_le_finrank`; and, through the public imports,
`Module.finrank`, `CategoryTheory.Limits.HasFiniteBiproducts`, `Preadditive`,
and `spectralNorm_unique_field_norm_ext`. Every proof dependency is thus available.
The docstring records all five proof steps: clopen ultrametric balls and ring
realization; finite biproduct coordinates; regular-module endomorphisms evaluated
on one and both inverse-matrix identities; evaluation at a chosen point; and the
two independent-family dimension inequalities. It does not assume field-valued
stalks or preservation of infinite sums by global sections.

Edge cases checked before writing:

- Rank zero on both sides uses empty biproducts and concludes `0 = 0`.
- If exactly one rank is zero, evaluating the two inverse matrices at a point
  would force a positive-dimensional vector space to be zero, so such an
  isomorphism is impossible; the statement correctly includes these cases.
- On the empty scheme all these sheaves can coincide, so the nonemptiness
  hypothesis is essential and retained explicitly.
- Disconnected, non-quasi-compact, nonreduced schemes and schemes of
  characteristic ℓ are allowed: one underlying point suffices for evaluation.
- E = ℚ_ℓ is included; no nontrivial extension-degree assumption is present.
- `u` is explicit, and both E and W can be in any common ambient universe.
  The site and coefficient value universes retain their required offset.

Searches made (actual tools and outcomes):

1. `msearch.py`, `leanfinder`, query
   `Finite free module objects over continuous p-adic coefficient sheaves on a nonempty scheme have invariant rank`:
   eight hits, including `Module.rankAtStalk_eq_finrank_of_free`,
   `Module.isLocallyConstant_rankAtStalk_freeLocus`, and
   `Module.rankAtStalk_eq_of_equiv`. These concern ordinary modules over rings,
   not this pulled-back condensed coefficient module category.
2. `msearch.py`, `loogle`, query `Mod.finiteFree, StrongRankCondition`:
   zero hits with the explicit diagnostic `unknown identifier 'Mod.finiteFree'`;
   the project-specific name is not indexed by that service. This is not used as
   evidence of absence on its own.
3. `msearch.py`, `grep`, query
   `finiteFree.*(rank|iso)|rank.*finiteFree|StrongRankCondition`, subdirectory
   `Algebra/Category/ModuleCat/Sheaf`: zero hits.
4. `msearch.py`, `leansearch`, query
   `An isomorphism between finite free continuous coefficient module sheaves over a nonempty scheme forces their two ranks to be equal`:
   eight hits: ordinary linear-equivalence dimension facts such as
   `LinearEquiv.finrank_eq`, `LinearEquiv.nonempty_equiv_iff_rank_eq`, and
   `SheafOfModules.freeFunctorCompPullbackIso`. None states the item for internal
   modules over pulled-back continuous condensed coefficients.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `continuous.*(rank|free)|finiteFree.*(rank|iso)|continuous-coefficient-free-rank`
   and then `finiteFree.*(rank|eq)|rank.*finiteFree|continuousCoefficientFreeRank|continuous_coefficient_free_rank`:
   existing finite-free constructors, continuous presentation matrices, and
   evaluation-coordinate dimension facts were found, but no item statement.
   In particular `ModuleObjects/Free.lean` defines the finite sums and is reused.
   `grep -rn 'lem-sfb-continuous-coefficient-free-rank' lean/WeilConjectures`
   found no declaration bound to this node.
6. The full proposed declaration name was searched in Mathlib, both project
   source roots, and `dag/lean_names_upstream.json`: no collision.

Validation: the first server compile identified the missing scoped transported
`MonObj` instance. Reading the upstream `MapMod` scope documentation diagnosed it;
adding `open scoped CategoryTheory.Obj` uses the existing canonical instance.
The final `scompile.py Q14 lem-sfb-continuous-coefficient-free-rank` run passed
both its sandbox and library-module compiles (12.6 s and 6.8 s), without warnings.
The signature has no auto-implicit variables, hidden `let` binders, or local notation.
All lines are at most 100 characters. There is one named theorem and one `sorry`.
No statement correction, disputed statement, or dependency defect was needed.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
