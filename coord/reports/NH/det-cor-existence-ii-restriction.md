## Worker report

Item: `det-cor-existence-ii-restriction`, group NH, stage 2, 2026-10-18.
Module: `Sheaf.Paper.ProperExceptionalRestriction`.
Declaration: `AlgebraicGeometry.ProEtale.CondensedRing.proper_exceptional_restriction`.
Only the item's `lean` record changes. No definition, helper node, dependency repair,
or statement correction was needed. The theorem has exactly one `sorry`.

Read the full item (including all five proof steps), its five statement dependencies,
their recorded source signatures/docstrings, the current blueprint statement/proof,
the stage-2 contract, H-fault list, example module and worker instructions. No repair
note exists for this item. The older local framework source has a stale unbundled
`compactificationOverField k f`; `scompile.py --source` confirms that the current
interface is `compactificationOverField p` for a morphism in `Over (Spec k)`, as
recorded in the dependency. The delivered statement uses that current interface.

Hypothesis-by-hypothesis correspondence:

- A commutative condensed coefficient ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`.
  Admissibility is `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`; its six alternatives
  include finite rings killed by an ell-power, Z_ell, O_E, Q_ell, E and Qbar_ell with
  their specified topologies. No finite-ring regularity or Gorenstein assumption occurs.
- The standing prime and positive-characteristic field are `(ℓ : ℕ) [Fact ℓ.Prime]`,
  `(k : Type u) [Field k]`, `[Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ ℓ)]`.
- Standing schemes and a morphism over k are `{X Y : Over (Spec (.of k))}` and
  `(p : X ⟶ Y)`. Both structure morphisms have `LocallyOfFiniteType`, `QuasiCompact`
  and `IsSeparated` instances. These are exactly separated finite-type k-schemes;
  their underlying schemes are `X.left` and `Y.left`.
- Properness is `[IsProper p.left]`, the recorded Mathlib notion. Universally closed
  implies quasi-compact, so its locally finite-type condition is finite type.
- The specified `Rp_!` and its Brown right adjoint are `localizingLowerShriek Λ
  (compactificationOverField p) h`, `G` and `_adj : ... ⊣ G`. Here `h` is only the
  membership proof needed to corestrict the already defined compactification functor.
  It changes no objects or maps and is provided by `exceptionalInverseImage_exists`.
  `G` and `_adj` name the already existing right adjoint of clause (3), rather than
  assume an extra geometric fact. Right-adjoint uniqueness makes this formulation
  apply in particular to the Brown witness of that theorem; no extra preservation
  hypothesis on `G` is imposed.

Clause-by-clause correspondence:

1. `∃ hStar : ∀ K, localizingClosureProEtale Λ X.left K → ... (Rp_* K)` states that
   the ambient pushforward restricts to the target hull. The following `Nonempty`
   natural isomorphism identifies the specified compact-support functor with exactly
   `(localizingClosureProEtale Λ Y.left).lift (L_X.ι ⋙ Rp_*) ...`.
   Here `Rp_*` is the actual generic total right derived functor
   `R((p.left)_*⟦Λ⟧)`, not an arbitrary functor, underived image, or bounded-only image.
2. The next conjunct quantifies over every `K : ConstantModelConstructibleFiniteTor
   Λ X.left` and asserts both `constantModelBoundedConstructible` and
   `DerivedCategory.finiteTorAmplitude` for its actual ambient pushforward. This is
   exactly preservation of Dctf.
3. The final existential gives `F₀` and `G₀` between the two recorded Dctf full
   subcategories. The equation for `F₀` after the ambient full inclusion says it is
   the restriction of that same `Rp_*`, on objects and maps. The equation for `G₀`
   says it is the restriction of that same `G`: first include Dctf(Y) in its hull,
   apply `G`, then include in the ambient derived category. `hSY` witnesses only
   the containment Dctf(Y) ≤ Loc(Dctf(Y)); it is an existential conclusion, not an
   added hypothesis, and follows from the defining intersection. `Nonempty (F₀ ⊣ G₀)`
   is the required right-adjoint assertion. In particular the restriction really
   lands in Dctf(X). Equalities specify the actual restrictions, not isomorphic
   replacements with unrelated actions on morphisms.

Dependency declarations used:

- `Sheaf.Paper.ExceptionalInverseImageExistence`:
  `AlgebraicGeometry.ProEtale.CondensedRing.exceptionalInverseImage_exists`, with the
  membership witness and Brown adjunction supplied there. It publicly imports
  `Sheaf.Paper.LocalizingExceptionalAdjoint`, whose `localizingLowerShriek` is the
  canonical `ObjectProperty.lift` of the compactification composite.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` (current
  bundled signature, read using `scompile.py --source`). Its compactification
  uses `HasCompactification.of_over` and the actual Nagata choice.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; its imported
  `Sheaf.Paper.LocalizingClosure` supplies `localizingClosureProEtale` and the
  generic intersection `CategoryTheory.localizingClosure`. These are used unchanged.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `constantModelConstructibleFiniteTor_wellDefined` and its imported
  `Sheaf.Paper.CondensedConstantConstructibility` declarations
  `ConstantModelConstructibleFiniteTor`, `constantModelBoundedConstructible`, and
  the generic `DerivedCategory.finiteTorAmplitude`. No alternate constructibility
  definition is used.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `ObjectProperty.lift`, `ObjectProperty.ι` and `ObjectProperty.ιOfLE` use Mathlib's
  actual full-subcategory constructions. The ambient pushforward is the module-object
  `CondensedRing.lowerStar` with its generic `Functor.rightDerivedFunctor`.

All recorded proof-dependency modules are imported without `public` unless already
needed for the statement. The proof docstring spells out the five DAG steps, including
identity Kan extension, the mate/triangle identity, the coefficient action, the
compactification comparison, repleteness, and the natural Hom bijection with inverse.
The Mathlib qcqs, composite-adjunction, mate and restriction modules are included too.

Edge cases checked: empty X or Y (whenever such a proper map exists), zero complexes,
the zero finite coefficient ring, nonregular finite rings such as Z/ell^2, the identity
proper map, all six coefficient alternatives, and arbitrary cohomological degrees.
None is excluded by a nonempty, nontrivial, dimension, smoothness, regularity or
bounded-degree assumption. All schemes and coefficients retain the framework's
universe u and u+1 respectively; no site-universe equality is introduced. The hull is
the dependency's ordinary ambient localizing intersection, with no derived-completeness
condition. No coproduct universe is independently changed by this delivery.

Searches (all via the prescribed tooling, with raw results in `searches.jsonl`):

- LeanFinder, “For a proper morphism derived compact support pushforward equals
  derived pushforward and Brown adjunction restricts to constructible complexes”:
  eight hits, headed by `SheafOfModules.pushforwardPushforwardAdj` and
  `SheafOfModules.pushforwardComp`; these are underived sheaf-module pushforward
  constructions, not this geometric derived compact-support restriction theorem.
- Loogle, `CategoryTheory.Adjunction.restrictFullyFaithful`: six hits, the generic
  restriction construction and its unit/counit/Hom formulas. Read its complete
  signature and docstring. It assumes the preservation comparisons, so it is a
  proof ingredient and does not already state this item.
- Mathlib grep, `proper.*[Ll]ower[Ss]hriek|[Bb]rown.*constructible`, `CategoryTheory`:
  zero hits.
- LeanSearch, “For a proper morphism compact support derived pushforward equals
  derived pushforward and its right adjoint restricts to bounded constructible
  finite Tor complexes”: eight hits, ordinary pushforward and pullback adjunctions
  on scheme modules / sheaves of modules. None states this theorem.
- `rg` of `det-cor-existence-ii-restriction`, proper/restriction/adjunction and
  localizing/proper patterns in `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no item match. Existing rational restriction,
  finite/integral proper-localizing and compactification-coherence modules supply
  parts of the proof but not the two-clause proper theorem with arbitrary admissible
  coefficients and the specified Brown adjoint. The new full declaration name was
  also searched and had no hit.

Validation: `scompile.py NH det-cor-existence-ii-restriction <module>` succeeds with
no diagnostics, compiling both its sandbox form (4.7 s) and library module (5.2 s),
within the required 60-second per-file limit. `autoImplicit false` is set; all
universes and variables are explicit. All Lean lines are at most 100 characters.
The node JSON retains indent 1, Unicode, a final newline, and only its `lean` delta.
No mathematical node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NH

The dispatcher brief requires a single worker and forbids starting other agents;
the maintainer supplies the independent delivery review. This section records the
worker's separate final consistency reread, not a claim of another worker's review.
Reopened the source statement, dependency interfaces and completed module. Verified
positive characteristic, ell invertible in k, separated finite type over the same k,
properness, all admissible coefficient cases, the actual chosen compactification,
the actual ambient derived lower star, its target hull membership, its Dctf
preservation, and the given G rather than an unrelated right adjoint. Checked both
restriction equations include maps and `Nonempty (F₀ ⊣ G₀)` has the correct direction.
The G₀ equation lands in the ambient derived category of X after applying G to the
canonical Dctf(Y)-to-hull inclusion; all its types are verified by compilation.
No missing clause, extra geometric hypothesis, hollow definition, new helper or
statement correction was found. No file-local notation or instance was introduced.
