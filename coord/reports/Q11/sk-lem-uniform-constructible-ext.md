## Worker report

The module `Sheaf.Paper.UniformConstructibleExt` states
`AlgebraicGeometry.ProEtale.uniformConstructibleExt`, with one `sorry` and no new definitions.
The DAG statement and its dependencies are unchanged; only the item's `lean` field is added.

Hypotheses and clauses, read against the current blueprint unit `_section.md` and the
four-step DAG proof:

- The standing global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its prime, finite field, fixed algebraic closure and their algebra structure are the
  existing construction, not replacements.
- The prime is `ℓ : ℕ` with `[Fact ℓ.Prime]` and `_hℓ : ℓ ≠ D.p`.
- The standing scheme may be over the finite field or its algebraic closure: `k : Type u`,
  `[Field k]`, and `_hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k)` allow either,
  including any isomorphic presentation of those fields. `[X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact ...]` and `[IsSeparated ...]`
  are exactly separated finite type over that base. No arbitrary positive-characteristic
  field of potentially infinite cohomological dimension is admitted.
- The condensed rational ring is `Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u+1}`,
  with its canonical `coefficientHeartRingObj Λ` and commutativity. `_hΛ` says precisely
  that Λ is the condensed ring of a finite subextension E of Qbar_l over Q_l, or the
  existing `Profinite.padicAlgClCondensedRing ℓ`. The latter is the finite-subextension
  valued condensed algebraic-closure coefficient ring, not all continuous Qbar_l functions.
- `C : ConstantModelConstructible (coefficientHeartRingObj Λ) X` is C in Cons(X,Λ),
  using the recorded finite constant scalar model predicate.
- `∃ d : ℕ` expresses an integer d_C >= 0. It occurs before both `∀ N` and `∀ q`, so
  depends only on C (with the standing scheme/coefficient data fixed).
- `∀ N : ConstantModelConstructible ... X, ∀ q : ℕ, d < q → ...` gives every
  constructible target and every degree above the bound, without target-dependent choices.
  Nonnegative natural degrees cover all integer degrees above a nonnegative integer.
- `Subsingleton (Abelian.Ext C.obj N.obj q)` is zero Ext in the ambient module category,
  not in the full constructible subcategory. `Abelian.Ext.homAddEquiv` identifies exactly
  this group with Hom_D(C[0],N[0][q]) of the ordinary unbounded derived category.
  There is a zero morphism, so Subsingleton says this abelian group is trivial.
- The second conjunct quantifies over every factorization `v : S ⟶ Z`, `i : Z ⟶ X`
  with v open and i closed, and an open `j : U ⟶ X` satisfying
  `Set.range i.base = (Set.range j.base)ᶜ`. Thus a is v followed by i and j is the open
  complement of Z, with the given scheme structures. No arbitrary map substitutes for a.
- Its `[CompactSpace S]`, `[QuasiSeparatedSpace S]` and `[QuasiCompact j]` are the
  domain conditions of the recorded cohomological dimensions. They exclude no stratum:
  X is Noetherian from the standing finite-type hypotheses; locally closed S is
  Noetherian, and every open in X is quasi-compact. An open immersion is quasi-separated.
  No finite-dimension assumption is added.
- `L : Mod ... (condensedRingObj (coefficientHeartRingObj Λ) S)` and
  `IsLisseCoefficientModule (coefficientHeartRingObj Λ) L` are a lisse Λ_S-module.
  The existing predicate means locally finite free, allowing varying finite ranks.
- The single-stratum source is literally
  `(CondensedRing.lowerStar ... i).obj ((CondensedRing.openImmersionLowerShriek ... v).obj L)`.
  This is i_*v_! L as specified by the coefficient-heart and closed-support nodes;
  it uses the given factorization, not a different lower-shriek construction.
- The equality `(d : WithTop ℕ) = relativeCohomologicalDimension ℓ ... j +
  cohomologicalDimension ℓ ... S + 2` specifies precisely the advertised d_C and asserts
  that it is finite, rather than extracting a meaningless natural value at infinity.
  The succeeding `∀ N ... ∀ q ... Subsingleton (Abelian.Ext ... N.obj q)` gives its
  claimed uniform vanishing. Natural d also gives nonnegativity.
- The explanatory two extra degrees are retained in the proof docstring: the support
  cone contributes one, and derived inverse limit of reductions contributes one.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.CohomologicalDimension`:
  `AlgebraicGeometry.ProEtale.cohomologicalDimension`, `relativeCohomologicalDimension`
  (qcqs domains, WithTop ℕ suprema), and its finite-type finiteness statements.
- `Sheaf.Paper.CondensedConstantConstructibility` (publicly imported through the heart):
  `IsConstantModelConstructible` and `ConstantModelConstructible`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, `coefficientRing`, with pullback of the actual ring structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: `CategoryTheory.Abelian.Ext`,
  and its `homAddEquiv` characterization of ambient derived Hom.
- `Sheaf.Paper.CoefficientHeart`: `coefficientHeart`, its assertion predicates; through
  its public imports, `coefficientHeartRingObj`, `IsLisseCoefficientModule` and
  `coefficientHeartLocallyClosedExtension`. The last is i_*u_! for the canonical closure;
  our displayed arbitrary factorization is the literal i_*v_! of that same node.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, as named in the
  recorded note for `sk-def-sf-setting`. Its recorded finite-stage vocabulary lives in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; this is a proof-only import,
  not an identification of rational pro-etale coefficients with finite etale coefficients.
- `Sheaf.Paper.FormalClosedSupport`: `CondensedRing.formalClosedSupportAssertions`,
  `FormalClosedSupportAssertions`, including the fiber and actual stratum expression.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` and the explicit standing-scheme binders
  are the recorded setting; the theorem does not need a new compactification choice.
- Proof imports also include `Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension`
  and Mathlib `Ext.ExactSequences` for both covariant and contravariant exact segments.
  The three detail estimates and `sk-lem-formal-closed-support-ii` have no recorded
  modules on this base, so no nonexistent proof import was invented. Their exact roles
  and the entire four-step proof are in the theorem's docstring.

Edge cases checked before drafting and again after compilation: C=0 admits d=0;
N=0 has zero ambient Ext; q=0 is not asserted to vanish; q=d is excluded by the strict
inequality. Empty X and empty S are allowed; the dimension convention makes empty
suprema zero, so an empty stratum has the harmless advertised cutoff cd(j)+2.
Both identity-open/full-closed and empty-closed/full-open factorizations are allowed.
L=0 is lisse of rank zero. No reducedness, smoothness, connectedness, geometric
irreducibility, Tor amplitude, integral lattice or completeness is added. Both finite
and algebraically closed base fields, and both rational coefficient choices, are covered.
All universes and variables are explicit (`set_option autoImplicit false`).

Searches (2026-10-18):

- `msearch.py ... leanfinder "For every constructible rational pro-etale sheaf C there
  is a uniform bound d such that Ext q C N vanishes for all constructible N and q
  greater than d"`: eight generic projective/injective-dimension hits, no geometric theorem.
- `msearch.py ... loogle "CategoryTheory.Abelian.Ext, CategoryTheory.HasProjectiveDimensionLT"`:
  eight generic dimension lemmas, including `HasProjectiveDimensionLT.mk'` and
  `ModuleCat.hasProjectiveDimensionLT_of_forall_finite`; none concerns these sheaves.
- `msearch.py ... leansearch "Uniform Ext vanishing for constructible rational pro-etale
  sheaves on finite type schemes over a finite field"`: eight unrelated condensed/etale
  geometry hits, no matching statement.
- `msearch.py ... grep "constructible.*Ext|Ext.*constructible|uniform.*Ext" CategoryTheory`:
  zero Mathlib hits.
- `rg` in the upstream WeilConjectures sources for the node id, proposed declaration
  name, uniform Ext and constructible/Ext patterns: no existing matching theorem.
  Generic uniform cohomological-dimension hypotheses are not this statement.
- `rg` in `lean/Sheaf`, especially Paper, for the same concepts: related continuity,
  sums and integral Ext statements; `IntegralConstructibleExt.lean` was read in full.
  It concerns integral coefficients and is not this rational bound with its explicit
  stratum formula. No duplicate of this theorem was found.
- `rg` of the proposed declaration in Mathlib, `dag/lean_names_upstream.json`, the
  upstream project and side library: no collision. The node's own source and current
  blueprint proof were both read in full.

No statement correction, new node, unusable dependency, or STATEMENT-DISPUTED finding.
Compilation: prescribed `scompile.py Q11 sk-lem-uniform-constructible-ext <file>` passed
both the sandbox and library-path compiles without errors or unexpected warnings.

## Second reading by Q11

A separate second pass in this worker reread the node, blueprint unit, dependency
signatures and completed file. No second agent was launched, as the dispatch brief
explicitly forbids it; the maintainer supplies the independent review of this delivery.
The pass checked the quantifier order C/d/N/q, nonnegative integer convention, ambient
Ext category, actual condensed coefficient ring, both base fields, complement equality,
lisse rank-zero case, both extension factors and equality with the finite explicit
cohomological-dimension sum. The corresponding Lean expressions are listed above.
No mismatch was found and no definition was duplicated. The node's statement, proof,
proof dependencies and statement dependencies remain verbatim from the base.
