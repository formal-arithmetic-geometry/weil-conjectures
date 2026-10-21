# Q41 stage-1 repair of lem-sfb-scalar-model-finite-flat-resolution

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-scalar-model-finite-flat-resolution.json: unchanged statement; 1055-character assembly in four steps.
- dag/nodes/sec-proetale-coefficients/lem-sfb-scalar-finite-free-resolutions.json: statement, unsplit, no Mathlib match; scalar DVR kernel/freeness and field finite-basis arguments.
- dag/nodes/sec-proetale-coefficients/lem-sfb-constant-finite-free-presentation-extension.json: statement, unsplit, no Mathlib match; exact constant-module sheafification and flat scalar extension of a specified presentation, with fixed matrix and basis identifications.
- dag/nodes/sec-proetale-coefficients/lem-sfb-ringed-finite-free-resolution-tensor.json: statement, unsplit, no Mathlib match; finite-free flatness, K-flatness, augmentation quasi-isomorphism and actual derived tensor coordinate model.
- citations.json: one verbatim statement quotation per step/node citation.

## Attachments

None. The upstream WeilConjectures source was searched by the item tag and scalar/resolution concepts. I read Sheaf.Paper.ScalarModelFiniteFlatResolution: both theorem bodies are sorry (DVR theorem line 172; field theorem line 225). The existing stage-2 statements do not end this deliberate stage-1 re-split.

## WANTED

None. All sources are local. No SGA source is used.

## Returned point repaired

The human required at least two comparable independent statement-only tasks, preservation of every old argument in new nodes, and at most 3000 characters of assembly. The final repair creates THREE such tasks, without dependencies between them. The parent has only four applications of their statements (1055 characters). All three have status unsplit, proof=[], proof_deps=[], proof_origin=null, complete sources, blueprint ancestry and actually run Mathlib searches. They can be assigned simultaneously.

The sandbox was initially empty except launcher marker files: there was no earlier node/report/search log to reuse. I copied the current live returned node. Every old proof step is preserved verbatim in the appendix, and every mathematical argument is assigned below. The item's statement and all maintainer metadata, including Lean records, remain unchanged. The first dry run passed for a two-node extraction; before pushing I corrected it to the stronger three-node extraction so none of the old arguments remains work in the assembly. No Lean, compiler, Lake, repository git command or extra agent was used.

## Argument conservation

1. Old step 1 and the field-basis portion of old step 8 become lem-sfb-scalar-finite-free-resolutions. Its DVR statement retains the chosen finite presentation's v and gives the actual kernel isomorphism. Incoming argument: the images u(e_j) generate ker v; each coordinate shows torsion-freeness inside R^n; lem-sc-dvr-fg-torsionfree-free gives R^m isomorphic to that kernel. Over a field delete a dependent vector using a nonzero relation coefficient; finite induction gives a basis, including the empty basis. These are substantive scalar algebra, independent of sheaves or tensor.
2. Old steps 2 and 3, and the constant/sheaf-extension part of old step 8, become lem-sfb-constant-finite-free-presentation-extension. The statement includes exactness of the constant module functor, preservation of finite powers, explicit balanced coordinate maps and inverses, the unchanged scalar matrix, and exact extension assuming flatness. It separately includes extension of a specified finite-free isomorphism with NO flatness hypothesis. These identifications must be made through module sheafification along the constant-ring unit; they are not an invocation of an unspecified exact functor.
3. Old steps 4, 5, 6, 7 and 9 become lem-sfb-ringed-finite-free-resolution-tensor. The statement includes the exact-sequence augmentation quasi-isomorphism (H^-1=0, H^0=M, all other H=0), and the degree-zero augmentation. It proves finite-free terms flat, then K-flatness, and fixes the tensor comparison, its factor order, coordinate maps and inverses, and conjugated differential. Incoming proof: finite coordinate kernels and successive common refinements for local epi lifts prove exactness of finite powers. Use bounded-above-flat K-flatness; choose a flat-term K-flat Q resolving N; descent applies to Q and K; f tensor id_K replaces Q by N[0]. Signed interchange is (-1)^(pq), checked against the two total differential terms, and its square is 1. Coordinates give (z_j) mapping to (sum_j a_ij z_j). Apply exactly the same computation to a single term for the field case. None of these arguments is shortened away: the old text below is the full incoming argument.

The extracted arguments have approximately 1.2K, 1.6K and 3.1K characters of incoming text, the last including the repeated field specialization. Each has its own objects and a distinct argument. No new node restates the parent: the scalar node has no site or tensor; the extension node starts with supplied scalar data over an arbitrary ring; the tensor node starts with supplied finite free sheaf data over an arbitrary ring sheaf and never constructs a scalar resolution.

## Sources read and searches

I read GOAL.md, the worker/stage-1 contract, the three levels in SETUP.md, delivery-errors.md B-E, and the item's chapter/unit records. The source route is the current main-20261015 Local models paragraph of det-def-localizing-closure-ctf-equals-bc. All three new nodes have that nearest blueprint ancestor and via=[lem-sfb-scalar-model-finite-flat-resolution], with their own precise place. There is no unit or chapter route change.

For lem-sfb-scalar-finite-free-resolutions, I read more-algebra.tex Tag 0AUW, lemma-dedekind-torsion-free-flat (3), lines 4954ff: finite torsion-free modules over a PID are finite free; DVRs are included. I read the statement of lem-sc-dvr-fg-torsionfree-free and the finite-presentation and DVR definitions. The blueprint's first Local models sentence supplies the length-one/length-zero assertion; the field argument is explicitly the finite-basis deletion argument retained below.

For lem-sfb-constant-finite-free-presentation-extension, I read sites-modules.tex Tag 03EI, lemma-sheafification-exact, lines 874ff. It treats module presheaf sheafification along O to O-sharp, so it applies to the constant ring presheaf. I opened the exactness node lem-weil-pbc-site-r-module-presheaf-sheafification-exact: (1) really gives sectionwise exactness and (2) finite limits and colimits, hence finite products and exactness. I read def-sf-site-constant-module-functor, def-weil-pbc-constant-sheaf, def-pur-sheaf-tensor-product and def-pc-flat-sheaf-modules. Their statements supply the precise construction and meaning, not a supposed theorem hidden inside a definition.

For lem-sfb-ringed-finite-free-resolution-tensor, I read sites-cohomology.tex Tags 06YQ lemma-bounded-flat-K-flat, 06YS lemma-K-flat-resolution, 06YP lemma-K-flat-quasi-isomorphism, and 06YU definition-derived-tor with its preceding descent construction. I also opened the actual statements of lem-pc-bounded-above-flat-kflat-site, lem-pc-kflat-resolution, lem-weil-pbc-site-derived-tensor-descent, lem-pur-kflat-tensor-quasiiso-independent and def-pc-tensor-complex-sheaves. K is bounded above and has flat terms; Q is also K-flat with flat terms, as the descent statement requires. Transport really is f tensor id_K, the form provided by the independent-universe invariance node. The signed interchange handles the desired order of factors and squares to 1. The generalized bounded-above statement requires only finitely many coordinates per degree, never a product over all degrees.

I searched the whole DAG by each Stacks tag and the relevant scalar/constant/free/presentation/tensor concepts and declarations. I searched the whole blueprint through blueprint_refs.py for finite free, scalar extension, K-flat, finite free resolution, constant module, discrete valuation ring and finite presentation. I opened close candidates including the condensed finite-integral resolution, finite-constant two-term resolution, scalar presentation cokernel, flat cyclic resolution, scalar normalized constant models, scheme K-flat single-tensor representative, native ringed tensor, and finite-free exact-sequence/projective-resolution lemmas. They do not state one of the three complete new assertions. The source-tag overlap comparisons are below. same_as=[] records the absence of a matching imported blueprint statement.

Every recorded new-node Mathlib search was actually run by msearch.py; searches.jsonl retains the queries, returned names and digests. Each node has LeanSearch, Loogle, source grep and two semantic phrasings. I read the source of promising hits: Module.FinitePresentation.exists_fin and exists_fin' (Algebra/Module/FinitePresentation.lean:84,94) give a quotient/right exact presentation, without its injective free kernel; PID.basisOfFiniteTypeTorsionFree' (LinearAlgebra/FreeModule/PID.lean:383) requires a separately proved finite torsion-free module and does not state the resolution with specified v. The scalar task needs that kernel argument and assembly, so is not a one-line specialization of either. Presheaf module sheafification's finite-limit preservation (Presheaf/Sheafification.lean:177-193), mapFree/mapFreeIso (Sheaf/Free.lean:184-207), presentation data (Sheaf/Quasicoherent.lean), ordinary-module tensor exactness (RingTheory/Flat/CategoryTheory.lean), and projective Tor (CategoryTheory/Monoidal/Tor.lean) supply useful components but not either sheaf assertion. Initial Loogle unknown-identifier queries were followed by corrected qualified patterns; they were not treated as absence evidence. A grep with a single-file subpath displayed malformed path fields from the wrapper; I reran it with its containing directory and retained the successful directory result, without modifying the tool.

## Review by Q41

I checked B-E against the sources and each actual node. Every new statement introduces all objects and hypotheses and references its non-elementary notions. The nodes are statement-only, without proof sketches in their statements. I checked C1/C4 at each application: assembly step 1 uses lem-sfb-scalar-finite-free-resolutions's DVR clause, whose finite presentation exists by the hypothesis on P; step 2 uses lem-sfb-constant-finite-free-presentation-extension's flat-extension clause with exactly the given flatness over R_C, then lem-sfb-ringed-finite-free-resolution-tensor's exact-sequence augmentation and tensor clause with the resulting specified matrix. Assembly step 3 uses lem-sfb-scalar-finite-free-resolutions's field clause and lem-sfb-constant-finite-free-presentation-extension's isomorphism clause, which explicitly needs no flatness. Assembly step 4 uses lem-sfb-ringed-finite-free-resolution-tensor's degree-zero augmentation and tensor formula with exactly that isomorphism. All these statements say precisely what is used; citations.json copies them verbatim once per step/node pair. No definition is cited as a substitute for an unproved exactness/comparison theorem.

I also audited the incoming proofs for the new tasks. The scalar kernel is torsion-free because the DVR is a domain; no claim that P is torsion-free is made. The exact sheafification statement actually includes the finite-product preservation needed to identify constant free terms. Flatness of B is not inferred from its algebra structure. Finite-free B-modules are shown flat over B using the coordinate exactness argument, not over R_C. Both resolving inputs meet the descent hypotheses; signed symmetry is checked at the differential rather than an unsupported claim of transport. These are the mathematical tasks the new nodes state and the preserved appendix passes to their future workers.

Small cases: P=0, finite rank zero, empty site and B=0 all give empty coordinate sums and zero complexes. For a one-point site with R a DVR and P=R/t, the scalar node yields the multiplication-by-t presentation, and the tensor node yields [N --t--> N], which may have nonzero H^-1. Thus no incorrect underived exactness is asserted for arbitrary N. Nonflat B=R/t destroys injectivity after extension of the scalar t-sequence, explaining exactly the flatness hypothesis in the extension node; its isomorphism clause still works. The field clause works for arbitrary B, with empty basis when P=0. The tensor node allows unboundedness below but not above; coordinate sums remain finite in each degree. The parent has no long proof step, total 1055<3000. Each old argument has moved to a new node, rather than merely being summarized. No statement dispute was found and no statement was weakened.

## Not duplicates

lem-sfb-constant-finite-free-presentation-extension vs lem-sf-intrinsic-realization-origin-comparison: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses IntrinsicRealizationOriginComparison, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-sfb-constant-to-continuous-scalar-flat: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses Continuous coefficients are flat over discrete constant PID scalars, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-weil-pbc-module-presheaf-sheafification-exact: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses Presheaves of O_X-modules form an abelian category with sectionwise kernels and cokernels, and sheafification is exact, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-weil-pbc-sheaf-tensor-closed: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses A-valued sheaves on an essentially small site: Grothendieck abelian, symmetric monoidal closed under the sheafified tensor product, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-sf-proetale-residue-module-tensor-homology: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses Ordinary tensor homology for modules over a constant field quotient, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-pur-constant-two-term-resolution: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses Two-term constant-sheaf resolution of Z/ell^N and its tensor augmentation, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-weil-pbc-site-r-module-presheaf-sheafification-exact: The new node transfers a supplied scalar presentation through the constant-ring module functor and flat scalar extension, fixing finite-power coordinate and matrix identifications; the existing node addresses Presheaves of R-modules on a site: sectionwise kernels and cokernels, and exact sheafification, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pe-kflat-roos-representative-invariance: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat representative invariance of augmented scalar-extension Roos cones, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-ringed-tensor-cohomological-bounds: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Cohomological bounds for derived extension of ring-sheaf scalars, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sbc-scalar-extension-counit-properties: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat computation and triangulatedness of a specified scalar-extension counit, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-exc-intrinsic-resolution-tensor-homology: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor cohomology in the intrinsic coefficient presentation, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-coef-derived-system-evaluation-calculus: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Coherent derived reduction, limit adjunction and fiberwise evaluation, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-finite-comparisons-existence: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Section preserving finite comparisons exist, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-finite-compatibility-transport: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Pinned finite comparisons preserve canonical open arrows, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-open-operation-models: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Open operation comparisons with fixed tensor models and right square, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-open-tensor-support: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor preserves open support in either factor, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-open-pullback-support: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived pullback preserves open support, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-exc-intrinsic-tor-amplitude-transport: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Transport of intrinsic Tor intervals, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-coef-finite-adjunction-diagram-realization: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Finite exceptional operations and enriched adjunction on coherent coefficient systems, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-finite-operation-comparisons: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Prescribed finite realizations admit pinned operation comparisons, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-coef-sheaf-flat-model: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Monoidal flat model for unbounded complexes on a ringed site, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-open-tensor-support-aux: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses The open tensor projection transpose is invertible, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-ringed-derived-native-tensor: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Native symmetric derived tensor and one-K-flat localization comparisons, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-integral-line-tensor-comparison-representative: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat line tensor models and finite balancing, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-coef-semilinear-operations-existence: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Geometric and coefficient operations on a fixed semilinear system calculus, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-coef-semilinear-system-existence: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Ordinary semilinear system calculus and cartesian internal Hom, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-proetale-derived-restriction-closed-monoidal: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Normalized native pro-etale restriction is braided closed monoidal, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-sf-open-normalization-data: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Geometric and operation data for open tensor normalization, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-trf-finite-filtered-flat-resolution: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Flat resolutions for a fixed finite filtration, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-trf-ringed-complex-derived-tensor-vanishing: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor cohomology vanishing for a complex on a ringed site, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-trf-split-flat-filtered-sheaf-models: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Split-flat finite filtered sheaf models and their canonical comparisons, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-single-tensor-representative: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses lem-pc-kflat-single-tensor-representative, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-model-shift-gauge: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Local supplied-tensorator shift gauge on flat telescope models, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-flat-truncation-telescope-comparison: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Quasi-isomorphism comparison for telescopes of truncation replacements, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-complex-hocolim-colimit: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Telescope homotopy colimits are termwise filtered colimits, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-derived-tensor-upper-bound: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor with a module preserves an upper cohomological bound, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-bounded-flat-replacement: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Bounded-above flat replacement on a ringed site, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-resolution: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Existence of K-flat resolutions on a ringed site, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-sc-bounded-flat-shift-representative: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Bounded-flat homotopy representatives and their translates, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-bounded-above-flat-tensor-acyclic: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensoring bounded-above acyclic complexes with bounded-above flat complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-normalization-morphisms: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Forward morphisms extending a bounded-flat normalization, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-kflat-localized-cone-presentation: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat cone presentation after homotopy localization, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-shift-gauge: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Source shift gauge for flat telescope normalization, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-hocolim-truncations: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Homotopy colimit of truncations, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-bounded-normalization-extension: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Extend bounded normalization through telescope cones, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-arrow-diagram: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Compatible flat tower diagram over a cochain arrow, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-bounded-above-flat-kflat-site: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Bounded-above flat complexes on a ringed site are K-flat, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-normalized-flat-telescope-stage-comparison: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Joint normalization natural on bounded-flat tower maps, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pc-derived-tensor-cohomology-vanishes: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Vanishing of derived tensor cohomology with an O_X-module, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-normalization-is-iso: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Invertibility propagates from bounded-flat models to telescopes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-normalized-flat-telescope-comparison: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Joint normalized pullback comparison on explicit flat telescopes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-tensor-counit-coordinate-equation: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Raw tensor coordinate equation for the universal pullback counit, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-normalization-unshifted-is-iso: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Invertibility on literal unshifted telescope cones, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-bounded-flat-model-normalization: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Supplied-tensorator normalization on bounded flat stages, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-sum-comparison-is-iso: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Invertibility of the restricted natural comparison on the sum of bounded-flat stages, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-source-kflat-tensor-left-triangulated: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor by a K-flat homotopy model is triangulated, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pc-kflat-complex: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat complex of modules on a ringed site, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-stage-map-refinement: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Common flat-tower refinement of a homotopy morphism, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-cone-normalization-descent: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Cone extension and descent of supplied normalized sum maps, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-sc-derived-tensor-augmentation: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor augmentation on a scheme, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pc-derived-tensor-complex-cohomology-vanishes: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Vanishing of derived tensor cohomology of two derived objects, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-sc-flat-telescope-stage-map: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Concrete flat telescopes and their stage-induced morphisms, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-sum-models: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Literal telescope models for a countable coproduct, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-closure: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Closure of K-flat complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-bounded-above-flat-tensor-acyclic-degree: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Fixed-degree exactness for bounded-above flat tensor complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sc-flat-telescope-stage-naturality: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Common-refinement cancellation extends stage naturality, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-cone-direct-sum: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Cones and countable direct sums of K-flat complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-geo-cartier-coeff-extension: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived scalar extension of a closed supported constant sheaf, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-condensed-support-projection-formula: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Natural support tensor projection formulas on unbounded condensed modules, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-sfb-ringed-projection-coherence-data: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Recorded data for tensor projection coherence, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-divisible-extension-derived-reduction: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived reduction of an extension by a divisible sheaf, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-ring-isomorphism-tensor-transport: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor and K-flat transport along a ring-sheaf isomorphism, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-constant-field-tor-bounds: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tor bounds over a constant field sheaf, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-ringed-site-point-kflat-resolution: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat resolution with K-flat stalk, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-flat-scalar-cyclic-resolution: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Two-term scalar quotient resolutions after flat sheaf extension, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-geo-cartier-exponent-independence: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Modulus change of the derived quotient and torsion identifications, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-sfb-condensed-pullback-tensor-comparison: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Normalized condensed-module pullback tensor comparison, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-adic-perfect-model-complete-reduction: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Completeness and residue calculation of a completed perfect coefficient model, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-ringed-projection-tensor-structure: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Canonical tensor structure in arbitrary recorded presentations, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-ringed-projection-pullback-comparisons: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Normalized identity, composition and section pullback comparisons, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-ringed-projection-tensor-compatibility: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor constraints and compatibility of normalized comparisons, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-ringed-projection-mate-exact: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Exactness data for the ringed-topos projection mate, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-completed-constant-resolution-tensor-calculation: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor quotient diagrams on finite-free completion resolutions, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-site-tensor-local-model-comparison: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor cohomology comparison from models of good truncations, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-weil-pbc-completed-constant-realization-data: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Completed constant realization interfaces, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-independent-bounded-flat-kflat: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Bounded-above flat complexes are K-flat at independent universes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-restriction-derived-products: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Exact scalar restriction on derived module sheaves is a right adjoint, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-split-perfect-tensor-kinjective: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensoring K-injectives with bounded split-projective complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-reduction-pullback-derived-tower: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Normalized derived pullback of a strict coefficient reduction tower, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-completed-adic-koszul-kflat: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flatness of the actual completed exterior Koszul complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-site-derived-tensor-descent: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor and K-flat representative descent on a ringed site, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-completed-constant-derived-tensor-tower: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Universal derived tensor tower from K-flat resolutions, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-pbc-kflat-fixed-tensor-triangulated: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Exact descent of tensoring with a fixed K-flat complex, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-etale-single-functor-monoidal-compatibility: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Canonical flat degree-zero tensor pairings and exact inverse image, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-functors: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Punctual tensor source and target functors, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-complexes: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Degree zero complexes and localization, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-line-unbounded-derived-tensor: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived tensor by a locally free line is the exact termwise equivalence, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-complexes-input-output: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Ordinary source and target tensor complexes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-integral-operations-well-defined: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-constructions: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Canonical quotient coefficient tensor arrow, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-derived-change-of-rings: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pur-integral-operation-shift-data: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Representative-normalized operation and independent-slot shifts, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-acyclic-kflat-tensor-arbitrary: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses An acyclic K-flat complex tensors acyclically with every complex, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs new-lem-kun-exact-monoidal-equivalence-derived: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Coherent monoidal descent of an exact adjoint equivalence, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-normalization: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived normalization by the quotient tensor map, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-kun-flat-resolution-existence: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Flat K-flat resolutions, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-amb-derived-tensor-symmetry-involutive: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Opposite canonical derived tensor symmetries cancel, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-iso: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived coefficient tensor isomorphism type, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-term-map: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Degree zero coefficient term map, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-localization-compatibility: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Localized termwise coefficient compatibility, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-kflat-tensor-quasiiso-independent: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses K-flat tensor transport for independent coefficient universes, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-system-tensor-reduction-formula: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor formula for actual semilinear reduction adjoints, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-completed-line-derived: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived finite reductions of a completed coefficient line are ordinary reductions, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-termwise-normalization: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Termwise normalization of the quotient tensor arrow, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-weil-completed-scalar-shift-descent: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Normalized descent of the strict completed scalar shift, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-kun-derived-tensor-well-defined: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Independence of the K-flat model, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-kun-prime-coefficient-pullbacks: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Canonical coefficient pullback maps, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-asd-derived-pullback-symmetry: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived pullback preserves canonical tensor symmetry, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-kflat-cone-comparison: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Two K-flat resolutions: augmentation square computing the derived-to-ordinary tensor comparison, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-system-normalized-tensor-closure: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Normalized semilinear systems are closed under tensor and inverse image, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pur-synchronized-canonical-maps: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses The same canonical map at two independent input families, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-weil-integral-derived-reduction: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Derived reduction of integral complexes modulo powers of the uniformizer, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-varying-ring-tensor-support: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Tensor support for canonical varying-ring extension, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-constant-two-term-resolution: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Two-term constant-sheaf resolution of Z/ell^N and its tensor augmentation, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pd-section-derived-realization: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Canonical derived section-module realization, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs def-pd-section-derived-tensor-data: The new node starts with a supplied bounded-above finite free complex over an arbitrary ring sheaf and proves its flat/K-flat coordinate tensor model for every N; the existing node addresses Canonical derived section-module tensor data, rather than that combined supplied-presentation/coordinate assertion.

lem-sfb-constant-finite-free-presentation-extension vs lem-sfb-scalar-model-finite-flat-resolution: The parent constructs a scalar resolution from a finitely presented DVR/field module and computes derived tensor. The new node assumes a scalar exact sequence over any R and only transfers its specified maps; it has no derived assertion.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-scalar-model-finite-flat-resolution: The parent constructs a scalar-model resolution over a DVR/field. The new node assumes a supplied finite-free complex and quasi-isomorphism over an arbitrary ring sheaf; it constructs no scalar resolution.

lem-sfb-constant-finite-free-presentation-extension vs lem-sfb-finite-constant-model-two-term-free-resolution: The existing node assumes the specific O_E/E condensed coefficients on a scheme pro-etale site; the new node transfers an arbitrary supplied scalar presentation on an arbitrary site and does not construct the scalar presentation.

lem-sfb-constant-finite-free-presentation-extension vs lem-sfb-scalar-presentation-cokernel: The existing node states cokernel preservation for the specified pulled-back condensed coefficients; it does not give injectivity after flat extension on arbitrary ringed sites.

lem-sfb-constant-finite-free-presentation-extension vs lem-sfb-scalar-normalized-constant-models: The existing node assumes a scalar-normalized additive equivalence to fixed-scalar sheaves and proves its transported local-model comparison; no such equivalence is assumed or used here.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sfb-locally-free-derived-scalars: The existing node treats derived change of rings of one locally free module; the new node treats a supplied multi-degree resolution and tensor with an arbitrary same-ring module.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pc-kflat-single-tensor-representative: The existing node assumes K-flatness over O_Y of a scheme and gives an abstract representative; the new node proves finite-free flatness/K-flatness on any ringed site and fixes all finite-power maps and differentials.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-sf-ringed-derived-native-tensor: The existing node supplies coherent derived monoidal comparisons conditional on K-flatness; the new node proves K-flatness for supplied finite free complexes and computes the coordinate differential.

lem-sfb-ringed-finite-free-resolution-tensor vs lem-pur-constant-two-term-resolution: The existing node fixes multiplication by ell^N on a constant Z_l sheaf and its quotient; the new node accepts arbitrary finite ranks and differentials over any commutative ring sheaf.

lem-sfb-scalar-finite-free-resolutions vs lem-sbc-root-normalization-generic-stalk-flat: the new node constructs a kernel basis for every specified finite presentation of an arbitrary DVR module and a finite basis in the field case; the existing node concerns Flat normalization stalks at the generic root divisor, rather than such an injective presentation with fixed quotient map.

lem-sfb-scalar-finite-free-resolutions vs lem-sc-dvr-fg-torsionfree-free: the new node constructs a kernel basis for every specified finite presentation of an arbitrary DVR module and a finite basis in the field case; the existing node concerns Finite torsion-free modules over a DVR are free, rather than such an injective presentation with fixed quotient map.

lem-sfb-scalar-finite-free-resolutions vs lem-sfb-finite-sum-lattice: the new node constructs a kernel basis for every specified finite presentation of an arbitrary DVR module and a finite basis in the field case; the existing node concerns Finite sums of valuation-ring lattices with their subspace topology, rather than such an injective presentation with fixed quotient map.

lem-sfb-scalar-finite-free-resolutions vs lem-weil-pbc-pid-torsion-free-module-flat: the new node constructs a kernel basis for every specified finite presentation of an arbitrary DVR module and a finite basis in the field case; the existing node concerns A torsion-free module over a principal ideal domain is flat, rather than such an injective presentation with fixed quotient map.

lem-sfb-scalar-finite-free-resolutions vs lem-pur-twist-integral-basis: the new node constructs a kernel basis for every specified finite presentation of an arbitrary DVR module and a finite basis in the field case; the existing node concerns The coefficient extension integers have a finite Z_l basis, rather than such an injective presentation with fixed quotient map.

lem-sfb-scalar-finite-free-resolutions vs lem-sfb-scalar-model-finite-flat-resolution: the scalar node has no sheaves or tensor conclusion; the parent must still assemble constant extension and the derived tensor calculation.

lem-sfb-scalar-finite-free-resolutions vs lem-sfb-finite-integral-condensed-resolution: the existing node fixes a finite O_E-algebra and proves continuous/topological condensed exactness with equal ranks, whereas the scalar node treats arbitrary finitely presented DVR modules with unrelated ranks and no topology.

lem-sfb-scalar-finite-free-resolutions vs lem-weil-pbc-finite-free-exact-sequence-resolution: that node assumes an already exact finite-free sequence and turns it into a projective resolution; the new node constructs the finite-free kernel of a specified right exact presentation.

## Original proof retained verbatim, with destinations above

### Old step 1

Assume first that $R$ is a discrete valuation ring. By the definition of finite presentation choose $R^a\xrightarrow{u}R^n\xrightarrow{v}P\to0$ with $a,n$ finite. Put $L=\ker v=\operatorname{im}u$. The finitely many vectors $u(e_j)$ generate $L$. If $0\ne t\in R$ and $t x=0$ for $x\in L\subseteq R^n$, each coordinate of $x$ is zero because $R$ is a domain. Thus $L$ is finitely generated and torsion-free. Apply [lem-sc-dvr-fg-torsionfree-free] to obtain an isomorphism $R^m\simeq L$, $m$ finite. Composing it with $L\hookrightarrow R^n$ gives $0\to R^m\xrightarrow{A}R^n\xrightarrow{v}P\to0$.

Cited nodes: def-sc-finitely-presented-module, def-sc-discrete-valuation-ring, lem-sc-dvr-fg-torsionfree-free.

### Old step 2

Form the constant presheaves of the scalar sequence. They are exact on every object, hence exact as presheaves by [lem-weil-pbc-site-r-module-presheaf-sheafification-exact](1). Apply its exact sheafification, clause (2), to get $0\to(R_{\mathcal C})^m\xrightarrow{A_{\mathcal C}}(R_{\mathcal C})^n\to P_{\mathcal C}\to0$. These are the constant module sheaves: by [def-weil-pbc-constant-sheaf] they are sheafifications of the constant presheaves. The identification of the two finite powers follows because sheafification preserves finite products, as asserted in clause (2) of the same exactness node.

Cited nodes: def-weil-pbc-constant-sheaf, lem-weil-pbc-site-r-module-presheaf-sheafification-exact.

### Old step 3

By the assumed flatness of $B$, the functor $-\otimes_{R_{\mathcal C}}B$ is exact, precisely the definition [def-pc-flat-sheaf-modules]; applying it to the preceding sequence preserves all three exactness assertions. For each finite $s$, identify $B\otimes_{R_{\mathcal C}}(R_{\mathcal C})^s$ with $B^s$ by $b\otimes(x_i)\mapsto(bx_i)_i$, with inverse $(b_i)\mapsto\sum_i b_i\otimes e_i$. The identities are the balancing relations, checked before sheafification and then sheafified using [def-pur-sheaf-tensor-product]. They also hold for $s=0$. Commutativity identifies the order of the factors used in the flatness definition with the order in $M$. The sequence is therefore $0\to B^m\xrightarrow{A_B}B^n\to M\to0$, where $A_B$ has exactly the scalar entries of $A$ mapped into $B$.

Cited nodes: def-pc-flat-sheaf-modules, def-pur-sheaf-tensor-product.

### Old step 4

Let $K^{-1}=B^m$, $K^0=B^n$, $d^{-1}=A_B$, and all other terms and differentials be zero. The epimorphism $B^n\to M$ gives an augmentation $K\to M[0]$. Injectivity of $A_B$ gives $H^{-1}(K)=0$, exactness in the middle and surjectivity give $H^0(K)=\operatorname{coker}A_B\simeq M$, and every other cohomology is zero. Thus this augmentation is a quasi-isomorphism by [def-weil-abstract-derived-category], so $K$ represents $M$ in the unbounded derived category.

Cited nodes: def-weil-abstract-derived-category.

### Old step 5

For any $B$-module sheaf $F$, the same coordinate maps give $F\otimes_B B^s\simeq F^s$. Finite powers preserve short exact sequences: kernels are computed in each coordinate, and a finite tuple of locally liftable sections has simultaneous lifts after successive common refinements of their finitely many covering families. Therefore tensoring with $B^s$ is exact, so $B^s$ is flat by [def-pc-flat-sheaf-modules], including $s=0$. In particular all terms of $K$ are flat. It is bounded above, with upper bound zero; [lem-pc-bounded-above-flat-kflat-site] now makes it K-flat. The augmentation of the preceding step is thus a K-flat resolution of $M[0]$.

Cited nodes: def-pur-sheaf-tensor-product, def-pc-flat-sheaf-modules, lem-pc-bounded-above-flat-kflat-site, def-pc-kflat-complex.

### Old step 6

Choose a termwise-flat K-flat resolution $Q\to N[0]$ by [lem-pc-kflat-resolution]. By [lem-weil-pbc-site-derived-tensor-descent], the total complex $\operatorname{Tot}(Q\otimes_B K)$ represents $N[0]\otimes_B^{\mathbf L}M[0]$. Apply [lem-pur-kflat-tensor-quasiiso-independent] to the quasi-isomorphism $Q\to N[0]$ and the K-flat complex $K$: it gives a quasi-isomorphism $\operatorname{Tot}(Q\otimes_B K)\to\operatorname{Tot}(N[0]\otimes_B K)$. This also computes the tensor with the factors in the stated order: on homogeneous factors of degrees $p,q$, the map $x\otimes y\mapsto(-1)^{pq}y\otimes x$ interchanges the total tensor complexes. Substitution in the differential formula of [def-pc-tensor-complex-sheaves] verifies the chain-map equation, and applying the map twice is the identity. It descends through the two resolving complexes in the cited tensor-descent statement.

Cited nodes: lem-pc-kflat-resolution, lem-weil-pbc-site-derived-tensor-descent, lem-pur-kflat-tensor-quasiiso-independent, def-pc-tensor-complex-sheaves.

### Old step 7

In $\operatorname{Tot}(N[0]\otimes_B K)$ the only terms are $N\otimes_B B^m$ in degree $-1$ and $N\otimes_B B^n$ in degree zero. Identify them with $N^m,N^n$ by $(z\otimes(b_j))\mapsto(b_jz)_j$, inverse $(z_j)\mapsto\sum_j z_j\otimes e_j$. The differential sends $(z_j)_j$ to $(\sum_j a_{ij}z_j)_i$, since $d_K(e_j)=\sum_i a_{ij}e_i$. These maps thus identify the complex with $[N^m\xrightarrow{A_N}N^n]$ in degrees $[-1,0]$, as asserted.

Cited nodes: def-pc-tensor-complex-sheaves, def-pur-sheaf-tensor-product.

### Old step 8

Now suppose $R$ is a field. A finite presentation supplies a finite spanning list of $P$. Delete a vector whenever the list is dependent: a nontrivial linear relation has some nonzero coefficient, and division by that coefficient expresses the corresponding vector as a combination of the others, so deletion preserves the span. Induction on the list length terminates in an independent spanning list $(p_1,\ldots,p_r)$. The map $R^r\to P$, $(c_i)\mapsto\sum_i c_ip_i$, is surjective by spanning and injective by independence, hence an isomorphism. This includes the empty list when $P=0$. Constant sheafification preserves this isomorphism, and since sheafification preserves finite products by clause (2) of [lem-weil-pbc-site-r-module-presheaf-sheafification-exact], the constant sheaf of $R^r$ is $(R_{\mathcal C})^r$. Tensoring it with $B$ and using the coordinate inverse of step 3 gives $M\simeq B^r$. This uses no exactness or flatness assumption on $B$ over $R_{\mathcal C}$.

Cited nodes: def-sc-finitely-presented-module, def-weil-pbc-constant-sheaf, def-pur-sheaf-tensor-product, lem-weil-pbc-site-r-module-presheaf-sheafification-exact.

### Old step 9

For the field case use $B^r[0]\simeq M[0]$ as the resolution. The coordinate exactness argument of step 5 proves that $B^r$ is flat over $B$, and [lem-pc-bounded-above-flat-kflat-site] makes this single-term complex K-flat. Choose $Q\to N[0]$ by [lem-pc-kflat-resolution]. Tensor descent identifies the derived tensor with $\operatorname{Tot}(Q\otimes_B B^r[0])$; [lem-pur-kflat-tensor-quasiiso-independent] identifies it in the derived category with $N[0]\otimes_B B^r[0]$. The latter is $N^r[0]$ by the coordinate maps. The degree-sign interchange in step 6 gives the stated order $M\otimes_B^{\mathbf L}N$.

Cited nodes: lem-pc-bounded-above-flat-kflat-site, lem-pc-kflat-resolution, lem-weil-pbc-site-derived-tensor-descent, lem-pur-kflat-tensor-quasiiso-independent, def-pc-tensor-complex-sheaves, def-pur-sheaf-tensor-product.

## Unfinished work

The three new nodes intentionally remain unsplit for independent workers. No Lean work is authorized or attempted. Final dry run and push follow this report.
