## Worker report

The module `Sheaf.Paper.DirectedGaloisFiniteTensorGenerators` states
`AlgebraicGeometry.Scheme.GaloisPartition.finite_tensor_generators`. Its sole theorem
has proof `sorry`; it introduces no definitions. The docstring carries all nine
proof steps of the DAG, including their dependencies. Source read directly:
ILO, Travaux de Gabber, Expose XVII, printed pp. 305--308 (PDF pages 311--314),
Propositions 7.4.2, 7.4.3 and 7.4.6, Definition 7.4.5 and Lemmas 7.4.4 and 7.4.7.
In particular the finite list is obtained from the finitely many simple
prime-field deck-group modules in 7.4.3 and the algebra argument of 7.4.7.

Clause-by-clause correspondence:

* Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`; the prime field is
  `ULift.{u + 1} (ZMod ℓ)`. The lift is the existing mixed-tensor API's
  universe presentation of the same field, not a new coefficient field.
* `X : Scheme.{u}` and `[IsNoetherian X]` state exactly the finite affine
  Noetherian-cover hypothesis. Mathlib's `isNoetherian_iff_of_finite_affine_openCover`
  gives the stated equivalence; neither characteristic nor invertibility of ell
  on X is imposed.
* `P : GaloisPartition X` is the already defined finite locally closed partition,
  with connected nonempty reduced domains and finite etale Galois covers.
  `GaloisPartition.galois` uses `PreGaloisCategory.IsGalois`, whose finite-etale
  specialization characterizes connected covers with simply transitive
  automorphisms on geometric fibres (`FiniteEtale.isGalois_iff`).
* `hP : P.IsDirected` supplies an ordering with closed complements of all initial
  segments, equivalently each next stratum is open in the remaining reduced
  closed complement. Its existential permutation is equivalent to the node's
  chosen ordering here: the conclusion depends on the partition, not its order.
* All objects are `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)`.
  This is the published constant-coefficient etale module-sheaf presentation,
  rather than a second category of module sheaves. Restrictions in
  `P.modules R` are exactly `Etale.upperStar`; the definition quantifies small
  filtered diagrams of finite successive extensions of local systems that
  become constant on the specified covers. It has no finite-type condition.
* `P.constructible R F` is precisely `P.modules R F ∧ IsConstructibleSheaf F`.
  The latter is finite stratification, etale local constancy and finitely
  generated module stalks. On Noetherian X the constructibility of the locally
  closed subsets in the upstream definition is automatic. It imposes no
  additional condition here. The published dependency exposes this predicate.
* `∃ (r : ℕ) (C : Fin r → ...)` is a finite list, and
  `∀ a, P.constructible ... (C a)` supplies both required properties of each C.
  This existential precedes **every** binder for A and E, so one list works
  simultaneously for all commutative Noetherian prime-field algebras. The ring
  is arbitrary `A : Type (u + 1)` with `[CommRing A] [IsNoetherianRing A]`
  and `[Algebra (ULift ... (ZMod ℓ)) A]`; no finiteness or flatness of A is added.
* For each constructible E in the class, `n` and the monotone chain
  `H : Fin (n + 1) → Subobject E` are a finite filtration in the ambient sheaf
  category. `IsZero (H 0 : ...)` is its zero initial term;
  `IsIso (H (Fin.last n)).arrow` says its final subobject is all of E.
  Each H j is explicitly required to satisfy `P.constructible A`.
* `Subobject.ofLE ... (hH (Fin.castSucc_le_succ i))` is the actual inclusion
  H_i into H_(i+1). Its `cokernel` is the ambient successive quotient.
  There is `a : Fin r` and `N : ModuleCat A` with `Module.Finite A N` for
  each quotient. `Etale.primeFieldTensorSheaf X ℓ A N` is the already published
  ordinary mixed tensor, sheafifying `N ⊗_Lambda C_a` sectionwise. This equals
  `N_X ⊗_{Lambda_X} C_a`, with A acting on N, and is not a derived tensor.
* The two displayed morphisms `ι` and `π` are morphisms in A-module sheaves.
  `ι ≫ π = 𝟙 _` is inclusion followed by retraction, identity on the quotient.
  It makes the quotient a direct summand of the specified tensor. A-linear
  mono/epi properties follow from the splitting; they are not new assumptions.
* For every E satisfying only `P.modules A E`, the second conjunct gives
  `I : Type (u + 1)`, `SmallCategory I` and `IsFiltered I`, with diagram D.
  Its stages satisfy `P.constructible A`; a cocone c with monic legs and
  `Nonempty (IsColimit c)` exhibits their filtered colimit. `c.pt ≅ E`
  identifies the apex with E. Composing the legs with this isomorphism gives
  actual constructible subobjects of E; cocone naturality and monic legs also
  force all transition maps to be monic. Thus this is a colimit of subobjects,
  not merely a diagram of abstract constructible objects.
* `(IsZero E → n = 0)` makes the zero object's filtration empty.
  `(IsEmpty X → r = 0)` supplies the stipulated empty-scheme list.
  Fin 0 has no quotient indices, so the retract assertion is vacuous for an
  empty filtration. The filtered presentation still has a nonempty indexing
  category, as required; the singleton constant zero diagram handles zero.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` and its finite-cover
  characterization.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (the general `SheafOfModules` presentation). For constant coefficients this
  delivery uses the already established ModuleCat-valued etale presentation.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` (used inside GaloisPartition).
* `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules`, exposing upstream
  `Scheme.IsLocallyConstantSheaf`, `IsFiniteSheaf`,
  `IsFiniteLocallyConstantSheaf` and `IsConstructibleSheaf` for the etale encoding.
* `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
* `Mathlib.CategoryTheory.Galois.GaloisObjects`:
  `PreGaloisCategory.IsGalois`; `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`:
  `Scheme.FiniteEtale.isGalois_iff`.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`.
* `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`;
  filteredness is `CategoryTheory.IsFiltered`. We use the universal-property
  witness directly, avoiding a second choice of a colimit object.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` exposes the recorded general tensor
  interface. In this theorem the ordinary tensor is its published
  constant-coefficient mixed presentation `Etale.primeFieldTensorSheaf` from
  `Sheaf.Paper.PrimeFieldTensorDevissage`.
* `Sheaf.Paper.GaloisPartitionModules`: `Scheme.GaloisPartition`,
  `.FiniteExtensions`, `.modules`.
* `Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement`:
  `GaloisPartition.constructible` and `.IsDirected`.

The partition definition node and the two definition-owner nodes below are added to
stmt_deps under brief-stage2 section 5. The theorem nodes for exact refinement and
prime-field devissage are not statement dependencies. Exact refinement remains a
proof dependency. There is no correction to the mathematical statement. The general tensor/module
interfaces need no repair: their existing etale presentations are available.
All already recorded modules of proof dependencies are imported without public;
unstated proof prerequisites are left for stage 3, not needed to type this statement.

Edge cases checked: empty X/empty partition; zero E and zero coefficient ring;
one stratum with identity cover; a cover with trivial or nontrivial deck group;
ell equal to the residue characteristic; infinite Noetherian coefficient rings
and finite A-modules with infinite underlying sets. No exceptional case is
excluded. Index and coefficient universes are both u+1, while schemes retain u
and the etale site's object/Hom universes retain u+1/u. No equality of these site
universes or independent undersized indexing universe is imposed.

Searches made:

* msearch.py LeanSearch, query “Constructible sheaves for a Galois partition have
  a finite filtration by summands of prime field tensors”: eight hits, including
  generic sheaf filtered-colimit and finite-type declarations, no theorem matching
  the finite uniform generator list.
* msearch.py LeanFinder, query “Finite prime field tensor generators for
  constructible sheaves trivialized on a fixed Galois partition”: eight hits about
  constructible spectra, condensed modules and Galois categories; no exact match.
* msearch.py Loogle, query
  `CategoryTheory.ObjectProperty.HasFiltration, CategoryTheory.Subobject`:
  zero hits, unknown HasFiltration identifier. The filtration is therefore
  expressed directly using the existing `Subobject` and `cokernel` notions.
* msearch.py Mathlib grep, query
  `GaloisPartition|finite_tensor_generators|primeFieldTensorSheaf`,
  CategoryTheory: no hits. Additional direct grep of Mathlib Subobject and
  ObjectProperty sources located the ambient-subobject and cokernel APIs.
* rg of the upstream WeilConjectures tree and lean/Sheaf for
  `GaloisPartition|galoisPartition|DirectedGalois|Unipotent|unipotent|TensorGenerators|tensorGenerators`
  found the existing partition, exact-refinement and prime-field tensor modules
  used above, but no theorem with this finite uniform list plus filtered-subobject
  presentation. The exact item-id search in WeilConjectures had no matches.
  The proposed theorem name also has no existing hit there or in
  dag/lean_names_upstream.json. No duplicate theorem is introduced.

Validation: scompile.py checked this module both as a sandbox module and under
its final library name, cleanly in 2.7 and 2.8 seconds. The initial use of bottom
subobject notation exhausted instance search; writing the mathematically
identical zero initial term and invertible final inclusion removes that issue
without a new hypothesis or increased limits. Every universe and variable is
explicitly bound. No STATEMENT-DISPUTED issue was found.


## New nodes

`def-per-directed-constructible-galois-partition` owns exactly the published plain
`GaloisPartition.constructible` and `GaloisPartition.IsDirected` definitions from
`Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement`, via `existing: true`.
The first is membership in `P.modules A` conjoined with `IsConstructibleSheaf`;
the second existentially orders all strata with closed complements after every
initial segment. ILO XVII Definition 7.3.5 distinguishes a supplied order from
the existence of one; the existing predicate expresses the latter, which is what
the generator statement needs. Its empty-order case is included. Definition
7.4.5 supplies the constructible subcategory. The construction is used for all
coefficient rings; the stated source's Noetherian hypotheses are required for
its subsequent finiteness assertions, not for forming this predicate.
Searches of all DAG definition records found no owner; the theorem node lists
these only as helpers. LeanSearch and LeanFinder found generic partition,
constructible-spectrum and locally constant-module APIs; Mathlib grep found no
exact notion. Full tool results are recorded in the new node. No Lean is copied.

`def-per-prime-field-tensor-sheaf` owns only
`AlgebraicGeometry.Etale.primeFieldTensorSheaf` from
`Sheaf.Paper.PrimeFieldTensorDevissage`, via `existing: true`.
It is the actual sheafification of sectionwise `ModuleCat.mixedTensor`, with
A acting on N. This ordinary tensor is the sheaf-degree operation in ILO XVII
7.4.1 and 7.4.6. Its definition also works for nonprime natural ell, exactly as
the existing signature does; the item itself retains the prime hypothesis.
There is no additional assertion of tensor exactness or zero-morphism
preservation in this new node. In particular the helper theorem from the
published module is excluded from its declarations. LeanSearch and LeanFinder
returned generic sheafification, tilde and locally constant module APIs;
Mathlib grep found no exact mixed prime-field sheaf functor. The upstream and
DAG ownership searches found no owner; the side theorem module already defines
it and is reused. Full tool outputs are recorded in the new node.

## Second reading by Q86

This is the dispatcher's required self-check; no independent agent was started.
I reread the saved theorem, its natural statement, both new definition records,
and the exact source signatures. The theorem's prime ell, Noetherian X,
directed partition, single finite list before all Noetherian A, constructibility
of that list, ambient finite filtration with constructible terms, ordinary mixed
tensor retractions with finite N, filtered constructible-subobject presentation,
zero filtration and empty-scheme list agree clause by clause with the mapping
in the Worker report above. The theorem signature and its Lean source are
unchanged from the returned packet. The two new records name only plain
existing definitions, with verbatim primary signatures and no theorem choice.
They require no additional assumptions in the item. The initial dry run of the
saved packet passed mechanically, but the explicit return still required this
ownership repair. The returned packet's two theorem additions to stmt_deps have
been replaced by the new definition nodes; exact refinement is still in
proof_deps. Current shared-main comparison showed only the intended lean and
stmt_deps changes for the item. The return identified the previous immutable
head c83333437f24 as identical to a46158355851; this packet now has two new node
files, changed item dependencies, and this revised report, so it is a substantive
repair rather than an unchanged redelivery. No mathematical correction or
STATEMENT-DISPUTED issue is involved.
