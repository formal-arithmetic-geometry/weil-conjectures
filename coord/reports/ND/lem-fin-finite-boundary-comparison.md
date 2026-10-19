## Worker report

States `AlgebraicGeometry.Etale.isIso_of_finite_boundary` in
`lean/Sheaf/AlgebraicGeometry/FiniteBoundaryComparison.lean`; its only proof is `sorry`.
The statement is unchanged, with no new nodes or dependency repairs.

Clause-by-clause correspondence:
- The implicit fixed commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`,
  following the recorded ordinary six-functor module-sheaf size convention.
- Schemes Y, S, G, Z are `{Y S G Z : Scheme.{u}}` with no finiteness, field, or
  Noetherian hypotheses.
- Proper b is `(b : Y ⟶ S) [IsProper b]`.
- The open immersion is `(a : G ⟶ Y) [IsOpenImmersion a]`.
- The closed complement is `(i : Z ⟶ Y) [IsClosedImmersion i]` together with
  `hcomplement : Set.range i.base = (Set.range a.base)ᶜ`.
  This allows any scheme structure on the stated closed complement.
- Finite bi is `[IsFinite (i ≫ b)]`, in Lean's diagrammatic composition order.
- Ordinary bounded-below module complexes K and L are objects of
  `_root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  The comparison is `(c : K ⟶ L)`.
- Invertible a*c is `hopen : IsIso
  ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.map c)`.
- Invertible Rb*c is `hpush : IsIso
  ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).map c)`.
- The conclusion is precisely `IsIso c`.

Dependency declarations read and used:
- `Sheaf.AlgebraicGeometry.DerivedCategories` records `DerivedCategoryModule` and
  Mathlib `DerivedCategory.Plus` for these module-valued étale sheaves. Its torsion
  predicate is imported as the dependency module but imposes no torsion assumption.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
  These act on arbitrary Grothendieck abelian coefficient categories, here ModuleCat.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, defined as the generic
  right derived functor of lowerStar, and exact pullback's `mapDerivedCategoryPlus`
  (documented also in `Etale.Derived.UpperLowerStar`).
- The conventions node expressly introduces no declaration. Mathlib `IsProper`,
  `IsOpenImmersion`, `IsClosedImmersion`, and `IsFinite` render its named properties.
- Every recorded proof-dependency module is imported non-publicly unless already
  imported publicly for the statement; Mathlib leaves are imported by their recorded files.
  The theorem docstring gives all six proof steps, including forgetting coefficients,
  taking a cone, closed-support recovery, derived composition, finite stalk products,
  and cohomological detection. There are no additional postponed helper theorems.

Edge cases: empty G (the whole source is closed), empty Z (the open covers Y), empty
Y or S, zero coefficients, zero complexes, and arbitrary degrees remain included.
No torsion, constructibility, finite coefficients, quasi-compactness of a, or
surjectivity of bi was imposed. Empty geometric fibres do not affect stalkwise
conservativity because no source geometric point lies over such a fibre. Properness
is retained even though the recorded proof does not use it. No statement dispute.

Searches (2026-10-15):
- msearch.py leanfinder: “A morphism of bounded below derived etale module sheaves is
  an isomorphism if it is on an open and its proper pushforward is an isomorphism with
  finite closed boundary”. Eight results, concerning module sheaf sectionwise isomorphisms,
  étale morphisms, and scheme isomorphisms; none is this derived detection theorem.
- msearch.py loogle: `IsIso, IsProper, IsFinite`: zero hits, unknown identifier IsIso.
- msearch.py grep: `finite.*boundary|boundary.*comparison`: five unrelated topology,
  manifold, and order/filter hits.
- rg of upstream WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json:
  `finite.*boundary|boundary.*comparison|lem-fin-finite-boundary-comparison`.
  Existing finite-boundary cohomology and reconstruction statements differ from this
  isomorphism criterion. No existing exact theorem or conflicting declaration found.
- Read the blueprint source file and the node's complete proof. Existing
  FiniteBoundaryReconstruction uses the same ordinary D+ and derived pushforward API.

Validation: compiled with the prescribed scompile.py wrapper; dry-run status below.

## Second reading by ND

Independent second reading, 2026-10-15. I read the sandbox node, its complete six-step
proof and Lean module, the original blueprint node and its enclosing compact-support
base-change unit, and all four statement-dependency records and their actual interfaces.
There is no statement_change, new node, or dependency module in this delivery.

The node's objects, hypotheses and conclusion, matched individually:

1. Fixed commutative coefficients: `(Λ : Type (u + 1)) [CommRing Λ]`. Correct:
   `DerivedCategories.lean` and its recorded six-functor encoding use exactly this
   coefficient size. No field, finiteness, torsion, nonzero-ring, or characteristic
   hypothesis appears. This is ordinary constant-coefficient module sheaves.
2. Schemes Y and S and proper b: `{Y S G Z : Scheme.{u}}`, `(b : Y ⟶ S) [IsProper b]`.
   Correct. Mathlib's `IsProper` extends separated, universally closed and locally
   finite type and supplies the properness convention; no base field or absolute
   finite-type assumption is imposed. Properness remains despite being unused by
   the mathematical detection argument.
3. Open subscheme G with inclusion a: `(a : G ⟶ Y) [IsOpenImmersion a]`. Correct.
   This allows every open immersion, without quasi-compactness or density.
4. Closed complement Z with inclusion i: `(i : Z ⟶ Y) [IsClosedImmersion i]` and
   `hcomplement : Set.range i.base = (Set.range a.base)ᶜ`. Correct: this states the
   exact underlying complementary subset and permits its closed subscheme structure.
   No reducedness or extra scheme-theoretic identification is assumed.
5. Finite composite bi: `[IsFinite (i ≫ b)]`. Correct: Lean's diagrammatic order is
   Z → Y → S. Mathlib's `IsFinite` is the finite morphism, not finite underlying
   sets or merely finite fibres.
6. Ordinary bounded-below complexes K,L on Y and their comparison c:
   `{K L : _root_.DerivedCategory.Plus
   (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (c : K ⟶ L)`.
   Correct: Mathlib Plus is the full bounded-below derived subcategory, rather than
   just nonnegative or bounded constructible complexes. The dependency's
   `DerivedCategory.torsionCohomology` is not assumed.
7. Invertibility on G: `hopen : IsIso
   ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.map c)`.
   Correct: I opened `UpperLowerStar/Defs.lean`: `upperStar` is sheafified left Kan
   extension, left adjoint to the recorded `lowerStar`. On the open immersion this
   is inverse image/restriction, and the exact-functor Plus operation is its
   termwise derived functor. It is not tensor pullback of structure-sheaf modules.
8. Invertible derived direct image: `hpush : IsIso
   ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).map c)`.
   Correct: `Derived/UpperLowerStarCoherence.lean` defines this as
   `(lowerStar _ b).rightDerivedFunctorPlus`. `lowerStar` in the recorded Defs module
   is evaluation on étale base change. The generic Grothendieck abelian and
   sheafification instances are available for this ModuleCat; none is an additional
   theorem hypothesis.
9. Conclusion: `IsIso c`. Correct, with arbitrary K,L and c quantified before the
   two invertibility assumptions. No extra conclusion and no existential substitute.

Source check: the original blueprint node has precisely these hypotheses. Its unit
restricts the compact-support base-change theorem at discrete coefficients, but this
auxiliary detection lemma explicitly concerns ordinary module complexes; it makes no
base-change assertion at unrestricted coefficients. I read Stacks etale-cohomology.tex,
`proposition-closed-immersion-pushforward` (04CA), and
`proposition-finite-higher-direct-image-zero` (03QP): they assume only a closed
immersion and finite morphism, respectively, for arbitrary abelian sheaves. Their
statements do not require Noetherian schemes, torsion, or constructibility.
I also read sites-cohomology.tex `lemma-cohomology-modules-abelian-agree` (03FD)
and `lemma-modules-abelian-unbounded` (0D6J), especially (3): the forgotten-coefficient
comparison applies to arbitrary ringed sites. Thus the proof's reduction to abelian
sheaves does not conceal a stronger coefficient hypothesis.

Edge cases: empty G, empty Z, empty Y, and empty S are included. An empty Z makes
its finite morphism vacuous but the open covers Y; an empty G reduces to finite
pushforward detection. Zero ring, zero K or L, identity/zero comparisons, arbitrary
negative lower bounds and degree zero remain included. No degree n or positive
integer is quantified, so no n = 0 exception or characteristic invertibility is
hidden. There is no external index type. `universe u` is bound; schemes are at u,
coefficients and module carriers at u+1 as in the dependency convention, and no
independent site universes have been forced equal. Larger coefficient data can be
placed in a common ambient size with the schemes; no fixed small coefficient set
has been selected.

Independent searches, with different phrases from the author:
- msearch LeanFinder: “Restriction to an open subscheme and derived pushforward
  jointly reflect isomorphisms when the complement is finite over the base”. Eight
  hits about scheme restrictions, structure sheaf maps and ordinary module forgetful
  reflection; none is this theorem.
- msearch Loogle: `"IsIso", "lowerStar"`: zero hits.
- msearch LeanSearch: “A map of bounded below etale sheaf complexes is invertible if
  its open restriction and pushforward are invertible and the closed complement is
  finite”: unavailable (Internal Server Error), no mathematical verdict inferred.
- msearch grep: `finite.*conservative|conservative.*finite`: five unrelated ergodic
  theory hits.
- Direct rg of upstream WeilConjectures, Mathlib and project lean/Sheaf for
  `finite_boundary|finiteBoundary|jointly.*(conservative|reflect)|boundary.*[Ii]so`.
  Opened the nearby `FiniteBoundaryReconstruction` and `DerivedOpenRestrictionDetectsIso`
  signatures: the former concerns constructibility with finite coefficients and
  finite-type schemes; the latter is Zariski locality of structure-sheaf modules.
  Neither is the present criterion. Generic joint-reflection lemmas do not name
  this étale finite-boundary pair. No usable exact existing declaration found.

H5/H6/H8/H9: no new definitions or hollow data; the sole theorem has exactly `by sorry`.
The module and theorem docstrings cite the source and blueprint id. The theorem's
six numbered steps carry the whole node proof: forget coefficients, cone,
closed-support recovery, composition and finite exactness, finite stalk products,
and cohomology detection/reflection. Statement and proof dependency imports are
present. No private notation/instance or unbound variable is introduced. The JSON
lean.statement was compared verbatim with the source signature and matches.

Mismatches found: none. Changes: appended this independent review only; the correct
Lean module and node record were left intact. Recompiled the delivered module through
scompile.py from the sandbox: both sandbox check and library check passed with no
errors or warnings.
