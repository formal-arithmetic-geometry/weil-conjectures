# Worker report: lem-per-noetherian-constructible-flat-lifting

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-constructible-flat-lifting.json: statement, split into seven proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-affine-free-presentation.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-etale-sum-constructible.json: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim statements for all fifteen step/node citations.

## Attachments

None. I searched WeilConjectures by the item id and by constructible/flat/lifting. AlgebraicGeometry.Etale.liftsAlongEpi_flat_isConstructibleSheaf, SixFunctors/Etale/Derived/Finiteness/FlatModel.lean:119, assumes [Finite Λ]; it does not state this item's arbitrary-Noetherian coefficient assertion. ConstructibleSheaf/FreeLifting.lean:484 likewise assumes [Finite Λ] for constructibility of free generators. Its exists_lift_freeYoneda at line 110 does allow arbitrary coefficients, but covers only the local-lifting subargument, which is written in the proof here using existing DAG inputs. No attachment of the entire item is claimed. The upstream master source is not used as proof evidence.

## WANTED

None. The item and both new inputs are in the local Stacks source.

## Findings and corrections

The item statement is unchanged. Its source proof is the finite-affine-generator lifting paragraph of Stacks 03TT, lemma-when-ctf, etale-cohomology.tex:13744-13800, using 095N (lemma-category-constructible-modules) and 03S8(3) (lemma-jshriek-constructible). I read both latter statements and proofs at lines 12412-12466 and 12185-12212. This is a lifting theorem for an arbitrary epimorphism p, with only G constructible: the construction does not assume B or C constructible.

An existing general-presentation node has an important interface mismatch: new-constructible-affine-free-presentation-general says Noetherian coefficients but points to def-constructible-constructible, whose finite locally constant convention, through def-constructible-finite, requires finite underlying stalk sets. In particular a constant R-module of value R for R=Z is permitted here but not by that referenced definition. Its Lean predicate may have a different intended module meaning; I do not take a Lean intention or another node's proof in place of its statement. The new presentation explicitly defines finite-type constructibility. No existing node was edited. This discrepancy should be repaired separately by the maintainer.

The new presentation is the full generators-and-relations theorem 095N, rather than the lifting-square assertion or a relabelled flat-cover clause. The new sum-constructibility input is 03S8(3) for arbitrary finitely generated coefficient modules, and makes no lifting or flat-cover assertion. Both remain statement-only. Their proofs are future items. Existing separating/free-representable comparison, exact forgetful functor, local surjectivity, finite affine refinement and flat sum-extension nodes are reused.

## Unfinished work

No required part of this split remains. Both new input theorems deliberately remain unsplit, as a one-level split requires. No Lean was written or compiled, no build tool was run, and no agent was started.

## Review by Q23

I checked the statement of the item against the affine-generator and lifting refinement paragraph of 03TT, and the statements of both new nodes against 095N and 03S8(3), including the qcqs hypotheses and the distinction between a finite module (finitely generated) and a finite underlying set. R=Z and M=Z pass both new statements: their underlying sets need not be finite. On X=Spec of an algebraically closed field the presentation is an ordinary finite module presentation and sum-extension on a finite etale object is a finite sum of the module. With an empty source j, extension is zero; on an empty X all module sheaves are zero. Both finite index families in the presentation may be empty. The zero ring is allowed.

Step 1 uses the locally-Noetherian quasi-separatedness statement to obtain the missing qs hypothesis from the finite Noetherian affine cover, then uses exactly the displayed epimorphic part of the new presentation. The presentation includes finite relations too and is strictly a generic input below the item. No assertion about the constructibility of B or C is used.

Step 2 uses the free-etale-module/shriek comparison statement for arbitrary commutative coefficients and the Hom formula explicitly present in the statement of the Mathlib separator node. Evaluation of an R-linear map R to F(W) at 1 is elementary, and its inverse sends r to r times the chosen section. This supplies both the components as sections and naturality for target maps and restriction.

Step 3 uses exactness of the forgetful functor to carry p to an abelian-sheaf epi; the cited local-surjectivity statement is expressly for abelian sheaves on this etale site and supplies the lifting covering sieve. The finite-affine-refinement node states membership of every chosen arrow in that sieve, not just that some cover exists. Its compactness hypothesis holds because U_i is affine. Thus all chosen restrictions actually lift. There is no use of sectionwise surjectivity on U_i and no supposed projectivity of a free etale sheaf.

Step 4 assembles the finite coproduct using the stated colimit existence. The natural Hom identifications give the commuting square summand by summand. I checked epicness using cancellation: a pair of maps equal on all refined generators agrees on each original section by the sheaf axiom, then on q, then on G. This argument is written out and is elementary given the cited Hom formula, so it hides no comparison lemma. The empty covering case is included.

Step 5 uses 03S8(3) exactly with M=R. Both X and each affine V_ik are qcqs, and R is generated by 1 as a module. Finite-sum constructibility follows by intersecting finite partitions and trivializing covers; finite sums of finite generator lists still generate. It does not use the finite-ring Serre theorem, whose hypotheses would fail for R=Z.

Step 6 checks every hypothesis of the existing flat sum-extension theorem: affine source implies separated, qc source and qs target imply quasi-compact, and etale implies locally of finite type, hence finite type. The coefficient ring there is any commutative ring. Tensoring with R is the identity via the displayed mutually inverse maps, so the input sheaf is flat. Tensor distribution over finite sums and finite direct-sum exactness finish the flatness of E. This does not cite a flatness definition in place of preservation of flatness by j_!.

Step 7 reindexes the finite pair family, and checks G=0, X empty and the zero ring explicitly. None excludes an edge case or introduces finiteness of R.

I searched the whole DAG by tags 095N and 03S8, by constructible/free/presentation/lifting terms, and the whole blueprint with blueprint_refs.py search (095N, 03S8, affine free presentation, constructible flat, locally constant finite type). I read the relevant finite-ring and general-labelled nodes and their referenced definitions before deciding on the new inputs. The current main-20261015 ancestor and the unit/chapter records were read; this is a generic coefficient-comparison input through the recorded ancestor chain, not a change to the perverse unit route. All off-unit statement inputs are declared as generic tool uses in split_report. No forbidden SGA route or citation is introduced.

The logged Mathlib queries include LeanFinder, LeanSearch, Loogle and source grep with two concept phrasings. I read the hits: freeYonedaHomEquiv supplies the Hom calculation already represented by an existing node; local-surjectivity theorems do not impose finite affine refinement; IsFinitePresentation and GeneratingSections refer to ringed-site local or global free presentations, not constructibility on strata. I read Generators.lean and Quasicoherent.lean (including IsFinitePresentation at lines 267-274) and Generator/Sheaf.lean:29-44; none gives 095N or 03S8(3). Records retain the actual query strings and outputs; invalid Loogle identifiers are labelled invalid, not mathematical evidence of absence.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files and sources: new statements introduce all objects and cite the definitions they use; proof_deps is the union of step uses; every cited statement was opened and is copied verbatim in citations.json. The item has no step over 2000 characters. The only interface correction was avoiding the finite-underlying-set definition mismatch; no item hypothesis or conclusion changed. The report's not-duplicate comparisons cover each same-tag pair. The required dry run below is the final mechanical check; its actual outcome is recorded after it exits.

## Not duplicates

lem-per-noetherian-affine-free-presentation vs lem-trf-constructible-generator-epimorphism: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-affine-free-presentation vs lem-trf-constructible-etale-ext-continuity: the existing statement is Ext continuity for constructible etale modules in affine inverse limits; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-trf-constructible-etale-finite-affine-syzygy: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-affine-free-presentation vs lem-trf-constructible-free-etale-resolution: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-affine-free-presentation vs det-brown-hypotheses-small: the existing statement is $\Dctf(X,\Lambda)$ is thick and essentially small; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-per-noetherian-constructible-galois-partition: the existing statement is Simultaneous Galois partitions for Noetherian constructible module sheaves; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-per-noetherian-ctf-flat-model: the existing statement is Constructible flat models for Noetherian coefficient rings; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-per-ind-etale-derived-hom-continuity: the existing statement is Derived sections and Hom along affine etale limits; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-per-noetherian-constructible-flat-lifting: the item constructs a commuting lifting square with a flat cover; this is only a general generators-and-relations presentation with no epimorphism-lifting square.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-finitely-presented: the existing statement is Constructible sheaves are finitely presented in the category of sheaves; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-finite-stalks: the existing statement is The geometric stalks of a constructible sheaf of modules are finite; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-finite-zero-cokernel: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-module-sheaf-colimit-constructible: the existing statement is A sheaf of $\Lambda$-modules on a qcqs scheme is a filtered colimit of constructible ones; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-finite-presentation: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-affine-free-presentation vs new-lem-weil-pbc-noetherian-module-finite-selection: the existing statement is Finite selection of module stalk detectors over a Noetherian ring; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-noetherian-descent: the existing statement is A constructible sheaf of $\Lambda$-modules on a qcqs scheme is the inverse image of one on a Noetherian scheme; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-etale-morphism-open-map: the existing statement is Etale morphisms are open; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-affine-free-etale-module-arrow-descent: the existing statement is Arrows between finite sums of affine etale free module sheaves descend; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-large-colimit-factorization: the existing statement is Constructible-source factorization into filtered colimits at the coefficient universe; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-limit-descent: the existing statement is A constructible sheaf of $\Lambda$-modules on a limit of qcqs schemes descends to some stage (Stacks 09YU (3), essential surjectivity); its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-support-constructible: the existing statement is The support of a constructible sheaf of modules on a qcqs scheme is well defined and constructible; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-field-point-factors-through-immersion: the existing statement is A point with values in a field lying over the image of an immersion factors through it; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs new-constructible-affine-free-presentation-general: the existing statement references def-constructible-constructible and hence finite underlying stalk sets; this new statement expressly permits infinite finitely generated module values (e.g. R=Z, F=Z_X).

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-algebraic-over-algebraically-closed-subfield: the existing statement is An element algebraic over an algebraically closed subfield lies in it; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-module-sheaf-colimit-constructible-data: the existing statement is Filtered constructible maps with factorization and relations; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-free-etale-module-shriek-comparison: the existing statement is Free representable module sheaves are etale extensions by zero; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-surjectivity-locus: the existing statement is Constructible locus of failure of module stalk surjectivity; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-etale-residue-field-extension-separable: the existing statement is Residue field extensions of an etale morphism are separable algebraic; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs new-constructible-limit-descent-general: the existing statement is Constructible limit descent for Noetherian coefficient modules; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-spectral-constructible-finite-intersection: the existing statement is In a spectral space, constructible sets with empty intersection have a finite subfamily with empty intersection; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact: the existing statement is In a spectral space an open subset is retrocompact iff it is quasi-compact; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-algebraic-extension-embeds-algebraically-closed: the existing statement is An algebraic extension embeds into an algebraically closed extension; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-spectral-constructible-clopen-constructible-topology: the existing statement is Constructible subsets of a spectral space are open and closed in the constructible topology; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-module-sheaf-colimit-constructible-cocone: the existing statement is Recognizing a colimit by constructible-source tests; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-spectral-constructible-topology-quasi-compact: the existing statement is The constructible topology of a spectral space is quasi-compact; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-affine-free-finite-stalk-generation: the existing statement is Finite affine free maps generating one module stalk; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-geometric-point-morphism-stalk-bijection: the existing statement is A morphism of geometric points induces a bijection of etale stalks; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constructible-module-finite-epimorphism: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-closed-immersion-residue-field-iso: the existing statement is A closed immersion induces an isomorphism on residue fields; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-field-point-factors-through-closed-immersion: the existing statement is A field-valued point in the image of a closed immersion factors through it; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-affine-free-etale-family-models: the existing statement is Common-stage models of two finite affine etale free families; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs def-weil-pbc-constructible-topology: the existing statement is The constructible topology of a topological space; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-weil-pbc-constant-subsheaf-generic: the existing statement is Generic constancy of a subsheaf of a constant finite sheaf; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-affine-free-presentation vs lem-sf-etale-flat-constructible-lifting: the existing statement is Flat constructible sheaves lift epimorphisms; its displayed conclusion is not the finite affine generators-and-relations presentation for every finite-type constructible sheaf over an arbitrary Noetherian ring.

lem-per-noetherian-etale-sum-constructible vs lem-trf-constructible-etale-finite-affine-syzygy: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-etale-sum-constructible vs lem-per-noetherian-ctf-flat-model: the existing statement is Constructible flat models for Noetherian coefficient rings; its displayed conclusion is not the constructibility of j_! of every finitely generated module over an arbitrary Noetherian ring.

lem-per-noetherian-etale-sum-constructible vs lem-per-ind-etale-derived-hom-continuity: the existing statement is Derived sections and Hom along affine etale limits; its displayed conclusion is not the constructibility of j_! of every finitely generated module over an arbitrary Noetherian ring.

lem-per-noetherian-etale-sum-constructible vs lem-per-noetherian-constructible-flat-lifting: the item constructs a commuting lifting square with a flat cover; this is only a general constructibility theorem for j_! of an arbitrary finite-type module, with no lift or cover assertion.

lem-per-noetherian-etale-sum-constructible vs lem-weil-pbc-constructible-module-finite-presentation: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-etale-sum-constructible vs lem-weil-pbc-affine-free-etale-module-arrow-descent: the existing statement is Arrows between finite sums of affine etale free module sheaves descend; its displayed conclusion is not the constructibility of j_! of every finitely generated module over an arbitrary Noetherian ring.

lem-per-noetherian-etale-sum-constructible vs lem-weil-pbc-constructible-module-limit-descent: the existing statement is A constructible sheaf of $\Lambda$-modules on a limit of qcqs schemes descends to some stage (Stacks 09YU (3), essential surjectivity); its displayed conclusion is not the constructibility of j_! of every finitely generated module over an arbitrary Noetherian ring.

lem-per-noetherian-etale-sum-constructible vs lem-weil-pbc-etale-free-sheaf-constructible-core: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-etale-sum-constructible vs lem-weil-pbc-constructible-generation: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-etale-sum-constructible vs lem-weil-pbc-etale-free-sheaf-constructible: the existing statement requires a finite coefficient ring or finite underlying module values; this new statement permits arbitrary Noetherian rings and infinite finitely generated values.

lem-per-noetherian-etale-sum-constructible vs lem-kun-03sa: the existing statement is Constructible generation; its displayed conclusion is not the constructibility of j_! of every finitely generated module over an arbitrary Noetherian ring.

