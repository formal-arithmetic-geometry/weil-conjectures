## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceModuleEventuallyProperSupport` states
`AlgebraicGeometry.AlgebraicSpace.module_eventually_hasProperAnnihilatorSupport`.
Its only theorem has proof `sorry`; it adds no definition or axiom. The statement
is the node's specialization of Stacks Tag 08K2 in Situation 084W. I read the
source at `literature/stacks-project/spaces-limits.tex`, labels
`situation-descent-property` and `lemma-eventually-proper-support`.

Clause-by-clause correspondence:

- Schemes and algebraic spaces over Spec Z: the common base is
  `Spec (CommRingCat.of (ULift.{u} ℤ))`. The lift keeps schemes in arbitrary
  universe `u`; the algebraic-space structure sheaf and module sections stay
  in their existing universe `u`, with the existing larger site universe.
- A small nonempty directed set: `I : Type u`, `[PartialOrder I]`,
  `[Nonempty I]`, `[IsDirected I (· ≤ ·)]`. The index and schemes use the same
  universe, as required by the project's limit convention.
- The inverse system of affine schemes is `D : Iᵒᵖ ⥤ Over (Spec ... ℤ)`;
  `haff` asserts each underlying scheme is affine, and `htrans` asserts each
  underlying transition morphism is affine. These are the actual scheme
  predicates, not predicates on arbitrary algebraic spaces.
- The limit T is `c.pt`, with its projections `c.π` and `hc : IsLimit c`.
  A limit in schemes over the terminal scheme Spec Z is precisely the given
  scheme limit, with its unique structural maps. The original stage is `i₀`.
- The finitely presented map is `f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀))`.
  Its three conditions are `hqc : MapIsQuasiCompact f₀.hom.hom`,
  `hqs : MapIsQuasiCompact (pullback.diagonal f₀.hom.hom)`, and
  `hlfp : MapIsLocallyOfFinitePresentation f₀`. These are exactly
  quasi-compactness, quasi-separatedness, and the local finite-presentation
  chart test. No separatedness or representability of f₀ is assumed.
- The quasi-coherent finitely presented module is `M₀ : X₀.QCoh` together
  with `hM₀ : M₀.obj.IsFinitePresentation`. The latter is Mathlib's finite
  local free-presentation predicate. No new module notion is defined.
- The limit fibre product X has projections `p` and `f`; `sq` is its sheaf
  pullback square with the actual Yoneda image of `c.π.app (op i₀)`.
- All stage products are `Xᵢ j`, where `j : {j : I // i₀ ≤ j}`.
  Their projections are `pᵢ j` and `fᵢ j`, and `sqᵢ j` is the sheaf pullback
  square using `D.map (homOfLE j.property).op`. Pullback squares are a
  presentation of the specified fibre products, with their universal
  property; these maps are not arbitrary unconstrained replacement maps.
- The ordinary tensor pullbacks M and M_j are literally
  `(moduleTensorPullback p).obj M₀.obj` and
  `(moduleTensorPullback (pᵢ j)).obj M₀.obj`.
- Scheme-theoretic support and properness over T appear together as
  `hsupp : HasProperAnnihilatorSupport f (...)`. Its definition specifies
  a representable closed immersion, proper composite, and equality of the
  closed-immersion ideal with the module annihilator on every affine open
  of every étale scheme chart. It is not merely a closed set or an arbitrary
  proper carrier. `MapIsProper` is separated, finite type, universally closed.
- The conclusion is `∃ j : {j : I // i₀ ≤ j},
  HasProperAnnihilatorSupport (fᵢ j) (...)`. Thus j is explicitly at or
  beyond i₀ and its actual pulled-back module has proper annihilator support.
- No flatness predicate appears anywhere in the signature.

Recorded dependency interfaces used (all signatures and relevant docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  `Hom`, schemes as locally affine locally ringed spaces and their morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `structureSheaf`, `Modules`, and `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, the full subcategory for Mathlib's
  `SheafOfModules.IsQuasicoherent`. Finite presentation uses
  `SheafOfModules.IsFinitePresentation` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback`, the left adjoint
  of the chart-normalized direct image, with ordinary tensor interpretation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, `MapIsProper`; quasi-compactness uses
  the publicly imported `MapIsQuasiCompact` from `ProperCurveModuli`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`:
  `HasProperAnnihilatorSupport`, reused without the unrelated flatness predicate.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the actual
  scheme Yoneda sheaf, owned by `def-trf-scheme-algebraic-space` (Q87,
  existing:true). The enlarged-site theorem is not needed to state this item.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, owned
  by `def-sfb-proper-curve-moduli`, supplies both `hqc` and `hqs`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` supplies
  `IsPullback` for the displayed squares. No theorem asserting existence or
  algebraicity of a chosen fibre product is used in the signature.
- The size-convention node is metatheoretic; its explicit `universe u`
  and the existing site/coefficient universe levels implement it.

The item's statement dependencies gain three already landed nodes:
`def-sfb-space-flat-proper-coefficient`,
`def-trf-scheme-algebraic-space`, and
`def-sfb-proper-curve-moduli`, naming the existing interfaces used
in the signature. No dependency node or mathematical statement is changed.
The already stated proof dependencies `lem-sfb-space-etale-chart-support` and
`lem-sfb-space-closed-ideal-correspondence` have plain proof imports. The other
seven proof dependencies currently have no Lean record, so have no module to import.

Edge cases checked before writing:

- The zero module has empty annihilator support, hence is allowed.
- Empty schemes and empty stage or limit fibres are allowed; no nonemptiness
  of any space or module stalk is imposed. The indexing set is nonempty,
  exactly as the node requires, and its tail contains i₀ itself.
- A singleton index set allows j = i₀ and specializes to the same properness
  condition after the canonical pullback comparisons.
- Non-flat transitions are permitted. The docstring explicitly uses the
  inclusion of the extended annihilator in the pulled-back annihilator,
  rather than the generally false equality of annihilator ideals.
- The ambient finitely presented space need not itself be proper: only the
  annihilator closed subspace is required proper.
- No Noetherian, reducedness, characteristic, or finite-generation assumption
  on the annihilator ideal has been inserted.
- Different choices of pullback representatives are all quantified, with
  their pullback universal properties, and introduce no restriction.

Searches made with `msearch.py O2 lem-sfb-space-module-eventually-proper-support`:

- `leanfinder`, query "Scheme theoretic support of a finitely presented module
  on an algebraic space eventually becomes proper over an affine inverse
  system stage": eight hits, including Mathlib affine-limit section vanishing,
  morphism equality descent, and nonempty closed-locus descent. None states
  this algebraic-space module-support theorem.
- `loogle`, query `"support", "proper"`: only the irrelevant
  `Lean.Lsp.ResolveSupport.properties` hit.
- `grep`, query `proper.*support|support.*proper|HasProperAnnihilatorSupport`,
  subdirectory `AlgebraicGeometry`: one documentation hit in
  `Mathlib/AlgebraicGeometry/Morphisms/Basic.lean`, no statement match.
- `leansearch`, query "Proper support of a finitely presented quasi coherent
  module descends from an affine inverse limit of algebraic spaces": eight
  hits for finite-presentation and quasi-coherence definitions/instances and
  scheme affine-property descent, no matching theorem.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, including the node id and proper/support
  patterns, found the reusable `HasProperAnnihilatorSupport` predicate and
  the scheme-only `ProperSupportDescent` theorem, not this space theorem.
  The node-id search in upstream found no occurrence. I inspected the
  scheme theorem: its source and target are schemes and its module data
  are scheme modules, so it does not supply this algebraic-space statement.

Validation: `scompile.py` compiled the delivered file in both sandbox and
library module modes, each in 2.1 seconds; no error and no warning other than
any expected `sorry` warning. The single postponed theorem carries the
node's complete five-step natural-language proof and source in its docstring.
No statement dispute, correction, new definition node, or dependency repair.

## Returned delivery repair

The return reviewed immutable head `15489464002d` and accepted the mathematics.
The sandbox retained that theorem signature and original dependency additions;
comparison with current main found changes only in `lean` and `stmt_deps`.
This repair refreshes the node from current main and retains only the authorized
Lean record and corrected dependency additions. The theorem signature is
byte-for-byte the same as the returned signature recorded in `lean.statement`.

1. Replaced `lem-trf-space-enlarged-etale-ringed-site-model` in `stmt_deps`
   with its existing definition owner `def-trf-scheme-algebraic-space`.
   Read that node's Q87 record and the full `schemeSpace` definition and
   docstring. The public import now directly names its recorded module
   `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, instead of
   `SpaceCotangentRingMap`.
2. Removed `lem-trf-space-fibre-products-etale-covers` from `stmt_deps`
   and its direct public import. The signature uses Mathlib `IsPullback`
   to specify its squares; the algebraicity theorem is justification,
   not a notion required to form the signature. No `proof_deps` change.
3. Added `def-sfb-proper-curve-moduli` to `stmt_deps` and directly public
   imported `Sheaf.AlgebraicGeometry.ProperCurveModuli`. Read its node
   record and the `MapIsQuasiCompact` definition/docstring; this is the
   existing owner of the predicate in both `hqc` and `hqs`.

No new node, definition, hypothesis, mathematical correction, or theorem
signature change is part of this repair.

Repair validation: the revised direct imports compile through `scompile.py`
in both sandbox and library module modes (1.9 seconds each), with no errors
or warnings. The recorded signature still matches the returned signature
verbatim, and every Lean line is at most 90 characters.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
