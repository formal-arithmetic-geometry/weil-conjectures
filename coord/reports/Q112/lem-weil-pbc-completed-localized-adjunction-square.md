## Worker report

The module `Sheaf.CategoryTheory.CompletedLocalizedAdjunctionSquare` states
`CategoryTheory.completed_localized_adjunction_square`, with one whole-proof `sorry`.
No definitions, dependency repairs, new nodes, or statement changes are needed.

Clause-by-clause correspondence:

- A commutative ring and t: `(A : Type r) [CommRing A] (t : A)`. B is the actual
  `Localization.Away t`, not a second ring equipped with an arbitrary map.
- The four linear categories: independent `Type uC`, `Category.{vC}` etc., with
  `Preadditive` and `Linear A` on C,D, and `Linear (Localization.Away t)` on C',D'.
  No equality between object or morphism universes is imposed.
- The integral linear adjoints: `P`, `Q`, `[P.Additive]`, `[Q.Additive]`,
  `[P.Linear A]`, `[Q.Linear A]`, and `(a : P ⊣ Q)`.
- The localized-coefficient linear adjoints: `P'`, `Q'`, their additive and B-linear
  instances, and `(a' : P' ⊣ Q')`. Their units and counits are those of a'.
- The two A-linear functors into the B-linear targets: `FC`, `FD`, their additive
  instances, and `hFC`, `hFD`. These say exactly that multiplication by s maps to
  multiplication by `algebraMap A (Localization.Away t) s`. This states restriction
  of scalars directly, with no independently chosen A-action on either target.
- The specified comparisons are `α : P ⋙ FD ≅ FC ⋙ P'` and
  `β : Q ⋙ FC ≅ FD ⋙ Q'`. The hypothesis unit and counit equations are `hη`, `hε`.
  Lean composition `≫` is left-to-right, reversing the source's written order.
- The new A-linear left functor is `Ptilde` with its additive/linear instances and
  specified `γ : P ≅ Ptilde`.
- The first three conclusion factors use the actual `a.ofNatIsoLeft γ`. They give
  its Hom-equivalence formula, its unit `a.unit ≫ Q(γ)`, and its counit
  `γ.inv ≫ a.counit`, respectively, at every object and every applicable arrow.
- `αtilde` is a natural isomorphism with exactly the prescribed component
  `FD.map (γ.inv.app N) ≫ α.hom.app N`. The following two factors are the transported
  unit and counit compatibility equations; β and a' remain unchanged.
- `PB`, `QB` have source and target the recorded `ScalarLocalization A _ t`.
  Their objects equal the original functors' object values, wrapped by the existing
  one-field wrapper. Their tensor-arrow formulas are respectively
  `b ⊗ Ptilde.map f` and `b ⊗ Q.map f`; both are additive and B-linear.
  These specify extensions on every arrow, since pure tensors generate the Homs.
- `FCbar`, `FDbar` land in C',D' themselves. Their unchanged object maps and all
  pure-tensor images are specified: `b ⊗ f` maps to `b • FC.map f` or `b • FD.map f`.
  In particular b = `(IsLocalization.Away.invSelf t)^n` gives exactly
  Fbar(f/t^n) = t^(-n) F(f), including n = 0. They are additive and B-linear.
- `aB : PB ⊣ QB` is an actual adjunction, not merely functor isomorphisms or triangles
  without a Hom bijection. Its unit and counit components are exactly the transported
  ones tensored with one, as stated by the next two universal factors.
- `αbar`, `βbar` have the required localized functor sources and targets. Their hom
  components are exactly `αtilde.hom.app N` and `β.hom.app M`. Since these are natural
  isomorphisms, their inverse components are determined too.
- The last two universal factors give both compatibility equations on EVERY object
  of the raw localizations, with the SAME primed adjunction a'.
- The final stable-full-subcategory applicability is covered by the unrestricted
  quantification over C,D,C',D' and their given adjunctions: instantiate them with the
  stable full subcategories and their restricted data. This clause adds no new ambient
  hypotheses to the theorem. Mathlib's `Adjunction.restrictFullyFaithful` provides the
  restricted adjunction via the ambient Hom bijections; its
  `map_restrictFullyFaithful_unit_app` and `map_restrictFullyFaithful_counit_app`
  identify ambient components. On literal full subcategories and strict restrictions
  these are the identical Hom modules and components. No triangulated structure,
  nonemptiness, essential surjectivity, or Karoubi envelope is assumed.

`HEq` is used only for arrows with existentially chosen functor endpoints. The preceding
object equalities identify those endpoints with the displayed original objects. Thus
these are exact component formulas, not formulas merely up to conjugacy or isomorphism.
Tensor order is scalar-first, as in the recorded localization. Tensor symmetry identifies
this with the source's Hom-first convention.

Dependencies read and used:

- `def-weil-linear-functor`: its Mathlib match is
  `Mathlib.CategoryTheory.Linear.LinearFunctor`, `CategoryTheory.Functor.Linear`,
  together with `Functor.Additive`. Used directly for all same-ring linear functors;
  hFC/hFD spell out the same definition along the indicated coefficient map.
- `def-weil-linear-scalar-localization`:
  `Sheaf.CategoryTheory.ScalarLocalization`, `CategoryTheory.ScalarLocalization`,
  with its category/preadditive/linear instances and `ScalarLocalization.localization`.
  The complete definition and tensor composition/localization formulas were read.
- Proof dependency `lem-sfb-adjunction-transport-left-iso`:
  `Mathlib.CategoryTheory.Adjunction.Basic`, `Adjunction.ofNatIsoLeft` and
  `Adjunction.homEquiv_ofNatIsoLeft_apply`. The actual transported adjunction appears
  in the statement, so this is a public import.
- Proof dependency `lem-pur-semilinear-scalar-localization`:
  `Sheaf.CategoryTheory.SemilinearScalarLocalization`, notably
  `ScalarLocalization.extension`, `extension_spec`, `extensionNatTrans`,
  `extensionNatIso`, `extension_comp`, and the two whiskering laws. Plain proof import.
- Proof dependency `def-weil-module-base-change`:
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, `LinearMap.baseChange` and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`. Plain proof import.

Sources: read the complete node and all its proof steps; opened the current blueprint's
finite-extension proof, whose last paragraph says rationalization preserves the integral
isomorphism and inherits coherence. Read Bhatt–Scholze Remark 6.8.15 from the local PDF:
ambient operations and adjunctions restrict to constructible subcategories when stable.
The theorem docstring carries all seven proof steps, including the B[1/1] identification.

Edge cases checked before and during statement writing: γ = identity; t a unit (including
1); t = 0 or nilpotent, so B is the zero ring; zero original ring; t-torsion Hom modules;
zero arrows and zero Hom groups; empty categories and empty stable full subcategories;
fractions with n = 0. None needs cancellability or faithfulness of the integral
localization functor. Localized Hom universes are max(r,v), supplied by the recorded
category, without collapsing the original site/category universes.

Searches (all using the prescribed msearch wrapper, recorded in searches.jsonl):

- LeanFinder: `Transport a compatible linear adjunction square along a natural
  isomorphism and raw scalar localization`: eight hits including Adjunction.localization,
  Localization.η_app/ε_app and functor_linear_iff; no whole-square transport theorem.
- Loogle: `CategoryTheory.Adjunction.ofNatIsoLeft`: five hits for the transport and
  its unit/counit/Hom formulas. This is the recorded proof leaf, used directly.
- Mathlib grep: `ofNatIsoLeft|localization_unit_app`, subdirectory CategoryTheory:
  23 hits in localization, adjunction lifting, triple and basic files; no whole item.
- LeanSearch: `Linear adjunction compatible comparison square scalar localization`:
  eight hits, including categorical adjunction localization and module scalar-extension
  maps; none states the given square transport with raw Hom tensors and fixed comparisons.
- Project rg: `completed-localized-adjunction-square|completedLocalizedAdjunction`
  in lean/WeilConjectures and lean/Sheaf: no match. Broader `ofNatIsoLeft` and adjunction
  square searches found specialized geometric applications, not this statement.
- The intended full declaration name is absent from dag/lean_names_upstream.json.

Validation: scompile.py compiled both the module-mode sandbox and actual library module
cleanly (4.8 and 6.1 seconds respectively). Initial tensor endpoint inference errors were
repaired by explicit source localization typing and fully inferred RHS tensor types.
No diagnostic commands remain. All variables and universes are explicitly bound.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q112

A separate clause-by-clause self-audit reopened the node and the final module, comparing
hypotheses, composition direction, four extended object maps, pure-tensor maps, both
transported compatibility equations, unit/counit components, comparison components, and
both localized compatibility equations. No semantic mismatch was found. The only repair
was the tensor endpoint inference described above. This is a self-audit, not an invented
independent reader: the dispatcher forbids starting other agents and the maintainer's
independent review reads the delivery, as specified in the dispatched brief.
