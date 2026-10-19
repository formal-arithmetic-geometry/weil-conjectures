## Worker report

The module states `AlgebraicGeometry.exists_section_proetaleCover_of_ring_retractions`,
with its proof postponed by `sorry`. It expresses the forward implication construction
in Stacks 098F, using the finite affine refinement of 098D and the retraction condition
of 0981. The source was read in literature/stacks-project/proetale.tex at
`lemma-w-contractible-proetale-cover` and `definition-w-contractible`.

Clause-by-clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`.
- The target affine scheme is literally `Spec (.of A)` throughout.
- Every faithfully flat weakly etale ring map: `hsplit` quantifies over every
  `B : Type u`, every `CommRing B` and every `Algebra A B`, assuming
  `Module.FaithfullyFlat A B` and `Algebra.WeaklyEtale A B`. Every ring map
  A → B equips B with exactly such an algebra structure; conversely the structure
  supplies its ring map `algebraMap A B`. There is no ind-etale restriction.
- Its ring retraction is `∃ r : B →+* A,
  r.comp (algebraMap A B) = RingHom.id A`.
- An arbitrary covering family is given by `(I : Type u)`, `(T : I → Scheme.{u})`,
  and `f : ∀ i : I, T i ⟶ Spec (.of A)`.
- The pro-etale covering condition is precisely
  `Presieve.ofArrows T f ∈ Scheme.proetalePrecoverage (Spec (.of A))`.
  This uses the dependency's actual Mathlib precoverage, including its
  quasi-compact covering condition and weak-etaleness condition.
- The original scheme coproduct is `∐ T`, and its induced map is `Sigma.desc f`.
- The section and identity are `∃ σ : Spec (.of A) ⟶ ∐ T,
  σ ≫ Sigma.desc f = 𝟙 (Spec (.of A))`.
- The explicit shared universe u permits all small schemes, rings, and cover
  indices within the chosen bound, following def-weil-size-convention.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (the scheme and affine spectrum dependencies).
- Sheaf.RingTheory.IndPrincipalZariski exposes the recorded
  `Algebra.WeaklyEtale` and `weaklyEtale_SpecMap_algebraMap_iff`; the former
  is used in the hypothesis and the latter supplies the ring/scheme bridge.
  Both its local source and the upstream equivalence signature/docstring were read.
- Mathlib.RingTheory.Flat.FaithfullyFlat.Basic: `Module.FaithfullyFlat`,
  the recorded faithfully flat notion for the algebraMap.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.proetalePrecoverage`.
- Mathlib.AlgebraicGeometry.Limits: the small discrete colimit instance,
  `Sigma.ι`, `Sigma.desc`, `sigmaOpenCover`, `disjoint_opensRange_sigmaι`,
  and `sigmaSpec`/`ι_sigmaSpec` for the proof dependency.
- Mathlib.AlgebraicGeometry.Morphisms.Basic:
  `IsZariskiLocalAtSource.iff_of_openCover`, available through the public imports;
  the source-locality proof dependency specializes it to `WeaklyEtale`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat.SpecMap_iff` (proof import).
- Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra:
  `Module.FaithfullyFlat.of_comap_surjective` (proof import).
- Open immersions and weakly etale scheme morphisms are the recorded Mathlib
  `IsOpenImmersion` and `WeaklyEtale` definitions, available through the imports.

Edge cases checked before writing: the zero ring gives an empty target and is
not excluded; the empty covering is possible precisely for the empty target and
has its empty coproduct section. No Nonempty, Nontrivial, or finite-index assumption
was added. Cover members need not be affine or quasi-compact individually.
Repeated indices in the finite refinement are allowed. Infinite original
coverings are retained; only the auxiliary affine refinement is finite.

Searches for an existing statement:

- msearch.py leanfinder: "Every pro etale covering of an affine scheme whose
  faithfully flat weakly etale ring maps split has a section to its coproduct".
  Eight hits, concerning ordinary etale morphisms, formal etale products and
  etale algebra descent; none state the requested section theorem.
- msearch.py loogle: `"Scheme", "section"`. Eleven hits concerning section rings
  and affine Zariski presieves; none state a splitting of a covering coproduct.
- msearch.py grep: `WContractible|wcontractible|wContractible`: no Mathlib hits.
- rg over upstream WeilConjectures and project lean/Sheaf for
  `WContractible|wContractible|wcontractible`: upstream IsWContractibleRing and
  its ring retraction theorems exist, but use a different structural hypothesis
  and do not give this theorem for an arbitrary pro-etale covering family.
- grep for the exact item id in upstream WeilConjectures: no hits.
- Read Mathlib Proetale.lean and the recorded dependency modules: no duplicate
  section statement found.

No statement correction, disputed statement, new nodes, or dependency repairs.
All theorem proofs are postponed; no definition is introduced.

## Second reading by NW

Read the item's full node and its four proof steps, Stacks proetale.tex
`definition-w-contractible` (0981), `lemma-proetale-affine` (098D), and
`lemma-w-contractible-proetale-cover` (098F), including their surrounding
covering definitions. These assume a commutative ring and an arbitrary scheme
covering; there is no field, Noetherian, separatedness, or characteristic
assumption. The requested section is the intermediate construction in the
forward implication of 098F, composed with the affine refinement map.

Object/hypothesis/conclusion inventory, checked against the Lean signature:

1. A commutative ring A: `(A : Type u) [CommRing A]`. Exact.
2. The affine target T = Spec A: `Spec (.of A)` in every target, map and
   identity. This uses the recorded `AlgebraicGeometry.Spec`, not an arbitrary
   scheme with an additional affineness hypothesis. Exact.
3. Every ring map A to B: `hsplit` quantifies over `(B : Type u) [CommRing B]
   and `[Algebra A B]`. An arbitrary ring map supplies this algebra structure
   by `RingHom.toAlgebra`; the map is then `algebraMap A B`. Exact.
4. Faithful flatness and weak etaleness of that map:
   `Module.FaithfullyFlat A B → Algebra.WeaklyEtale A B → ...`.
   Read the former's class in FaithfullyFlat/Basic.lean and the latter's actual
   class in Mathlib/RingTheory/Etale/Weakly.lean: flatness of B and of tensor
   multiplication. Read the dependency module IndPrincipalZariski and its
   public imports, and upstream `weaklyEtale_SpecMap_algebraMap_iff` signature.
   This is weakly etale, not the distinct ind-etale predicate. Exact.
5. A ring retraction of every such map: `∃ r : B →+* A,
   r.comp (algebraMap A B) = RingHom.id A`. The direction is B to A and the
   composite is identity on A. Exact.
6. An arbitrary small family of schemes and morphisms to the affine target:
   `(I : Type u) (T : I → Scheme.{u}) (f : ∀ i : I, T i ⟶ Spec (.of A))`.
   Read `Scheme` and `Scheme.Hom`/`Spec.map` in Mathlib Scheme.lean. No
   affineness or quasi-compactness is required of individual members. Exact.
7. The family is pro-etale: `hcover : Presieve.ofArrows T f ∈
   Scheme.proetalePrecoverage (Spec (.of A))`. Read Proetale.lean's definition
   as `propQCPrecoverage @WeaklyEtale`, and the quasi-compact cover interface
   in Sites/QuasiCompact.lean and Cover/QuasiCompact.lean (finite affine-open
   refinements of compact target subsets). Thus this is the actual fpqc
   covering condition plus weak etaleness of every arrow, rather than only
   joint surjectivity or membership of the generated sieve. Exact.
8. The original scheme coproduct and its induced map p:
   `∐ T` and `Sigma.desc f`. Read the small discrete-colimit instance,
   `sigmaOpenCover`, and `disjoint_opensRange_sigmaι` in Mathlib Limits.lean;
   these are the recorded coproduct dependency. Exact.
9. Existence of a scheme morphism section with the prescribed identity:
   `∃ σ : Spec (.of A) ⟶ ∐ T, σ ≫ Sigma.desc f = 𝟙 (Spec (.of A))`.
   Lean composition is left-to-right, so this says p composed with σ is id.
   There is no demand for a single covering member to admit a section. Exact.
10. Size convention and quantifiers: `universe u` is explicitly bound and all
    rings, scheme sizes and covering indices are in the chosen bound. This
    includes the auxiliary finite product of affine coordinate rings needed
    in the proof; no independent smaller test-algebra universe makes the
    splitting hypothesis vacuous. All family data follow `hsplit`, and σ is
    existential after the covering hypothesis. Exact.

Also opened all statement-dependency records and the proof-dependency records.
For the proof interfaces read Mathlib `IsZariskiLocalAtSource.iff_of_openCover`,
the WeaklyEtale source-locality instance, `sigmaSpec` and `ι_sigmaSpec` and its
finite-index IsIso instance, `Flat.SpecMap_iff`, and
`Module.FaithfullyFlat.of_comap_surjective`. They give precisely the operations
used by the four docstring steps and are accessible through the delivered
public imports or the two ordinary proof imports. No dependency repair, new
node, or private replacement is needed.

Edge cases: the zero ring is allowed, hence the empty affine target is allowed.
The empty index type is allowed; an empty covering forces the target empty and
its coproduct has the required unique section. Infinite covers and repeated
indices are allowed, with only the intermediate refinement finite. There is
no Nonempty, Nontrivial, finite-index or characteristic hypothesis. No degree n,
coefficient category, or zero module is present. Universe u is bound explicitly;
all types in the signature are explicit or inferred from these bound data.

Independent duplicate searches, using different wording from the worker:

- `msearch.py ... leanfinder` with “A covering family of an affine spectrum with
  retractions of faithfully flat weakly etale algebras is split”: eight hits on
  etale algebra descent, etale loci and field product decompositions; none is
  this scheme coproduct section theorem.
- `msearch.py ... loogle` with `"Sigma.desc", "Scheme"`: zero hits.
- `msearch.py ... grep` with
  `proetale.*section|section.*proetale|ring_retractions`: zero hits.
- Fresh LeanSearch attempt with the disjoint-union formulation returned
  Internal Server Error; recorded as unavailable, with no negative verdict.
- Independently searched upstream WeilConjectures, the exact group-clone
  lean/WeilConjectures framework, and project lean/Sheaf for covering/section
  and covering/splitting combinations. Opened AlgClosedFieldSite.lean:
  its theorem requires an algebraically closed field and concerns covering
  sieves, so it cannot replace this theorem for an arbitrary ring.
  Read coord/pefw-upstream-framework.md; none of its attached declarations
  states this result. Ring-level retraction facts likewise do not state the
  geometric section of an arbitrary original covering coproduct.

No mismatch found; no Lean or node changes were warranted. The docstring has
all four node proof steps with their named dependencies, source tags and
blueprint id. The only declaration is a theorem with proof `sorry`; no hollow
definition, proved helper, local notation or hidden universe was introduced.
The recorded lean.statement is verbatim the file signature.

Server compilation via scompile.py succeeded cleanly: dependency overlay
IndPrincipalZariski 1.3 seconds, delivered WContractibleCoverSection 1.4 seconds,
nice 19, two threads, 60-second per-file limit. No compiler warnings or errors.
