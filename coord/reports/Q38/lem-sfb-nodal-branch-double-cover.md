## Worker report

Repair by Q38 of the human re-split return dated 2026-10-22. The sandbox was empty at start, so the current repository node (with the eleven reviewed steps named by the return) was copied. No retained report or searches existed to overwrite. No repository or launcher file, Lean file, compiler or Lake command was written or run.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-branch-double-cover.json: existing item; statement unchanged; seven-step assembly, fewer than 3000 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-graph-cone-gluing.json: statement; unsplit, no Mathlib match; owns old Steps 2, 3.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-graph-cone-chart.json: statement; unsplit, no Mathlib match; owns old Steps 4, 5.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-graph-cone-base-change.json: statement; unsplit, no Mathlib match; owns old Steps 7, 8.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-graph-cone-fibre.json: statement; unsplit, no Mathlib match; owns old Steps 9.

## Attachments

None. Project source WeilConjectures was searched for the blueprint tag and nodal/branch concepts. Sheaf.AlgebraicGeometry.NodalBranchDoubleCover contains `nodal_branch_double_cover` with `sorry` (lines 357-358); it cannot close the item. NodalBranchScheme also has a sorried immersion theorem. General Mathlib Proj, normalization and etale declarations do not state the proposed obligations.

## WANTED

None. The cited Stacks TeX files are available locally.

## Fault and repair

The return is a workload-size objection, not a mathematical correction: the old proof has 10497 characters. Its statement, graph-cone route, and all previously established arguments are retained. Four new nodes are statement-only, status unsplit, proof [], proof_deps [], proof_origin null; subsequent workers can start them separately (the gluing interface is a statement dependency for the other three). They are not a single relocated double-cover theorem: they respectively establish affine graph gluing for an arbitrary closed inclusion, the explicit graded nodal chart, the nonflat graded base-change comparison, and the field graph-local tangent comparison. The parent still proves the finite etale descent, finite-presentation and proper-finiteness clauses. No new node asserts all the parent's conclusions.

## Search and duplicate review

Before creating nodes I searched the whole DAG by the source tags and graph/conormal/nodal words, the whole imported blueprint with tools/blueprint_refs.py search (graph, graph conormal, nodal, 0CBY, 0CBT), and the Lean project by blueprint tag and nodal/branch concepts. Ancestor lookup returns None for this inherited source chain; new nodes preserve that and extend its via list, with the exact old steps appended to from.place. No matching blueprint statement was found.

Each new node has two distinct LeanFinder phrasings, a LeanSearch query, a Loogle name query, and a Mathlib AlgebraicGeometry grep, exactly as logged by msearch.py. I read all returned signatures. Gluing hits are closed-subscheme quotient gluing or ordinary Proj charts, not graph ideal-power gluing; chart hits are etale definitions/standard presentations, not uv=h graph-cone calculations; base-change hits are preservation of smoothness/finite presentation or cotangent-complex maps, not nonflat associated-graded isomorphisms; fibre hits are relative normalization maps and Weierstrass point ideals, not graph-versus-local tangent comparisons. Loogle returned the overload message for all four queries, recorded as unavailable even though its wrapper sets ok=true. LeanSearch and both LeanFinder phrasings succeeded, as did the four source greps. None is a Mathlib leaf.

## Not duplicates
lem-sfb-graph-cone-gluing vs def-pur-finite-smooth-canonical-interfaces: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Normalized extended-Rees and relative-Spec cone comparison. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-pur-rees-cone-normalization: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Degree-one normalized comparison predicate. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-sfb-nodal-branch-scheme: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns The graph-exceptional-fibre construction of the relative nodal branch scheme. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-trf-fine-log-etale-descent-datum: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Fine logarithmic structures and labelled etale descent data. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-augmented-module-complex-glue-data: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Strict descent data for augmented module complexes. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-finite-ring-torsor-associated-module: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Associated module sheaf functor with arbitrary commutative coefficients. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-proetale-local-submodule-gluing-data: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns A module with compatible local identifications. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-proetale-local-subobject-kernel: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Kernel construction and factorization API for local subobjects. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-site-module-compatible-tuples: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns All-test-object compatible tuples of local module sections. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-torsor-associated-module: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Associated module functor of equivariant locally constant sections. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs def-weil-pbc-torsor-section-representation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Canonical representation on sections over a torsor. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pe-set-sheaf-cover-descent: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Effective descent and morphism gluing for sheaves of sets along a covering. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pe-site-sheaf-gluing: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Effective gluing of sheaves of sets on localized sites. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-per-generalized-blowup-class: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Modified-blowup construction with a conormal presentation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-clopen-ringed-module-gluing: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Exact module gluing across a finite clopen cover for arbitrary ring sheaves. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-algebra-affine-generators: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Affine homogeneous generators of a conormal presentation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-cone-hom-ext: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Degree-one uniqueness for maps to conormal spectra. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-graded-algebra: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Conormal graded algebra on a closed subscheme. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-graded-algebra-basic: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Fixed conormal powers, tensor-pullback pieces and representative maps. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-graded-algebra-construction: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Total conormal algebra and normalized affine charts. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-graded-algebra-hom-ext: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Degree-one uniqueness for conormal algebra morphisms. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-graded-algebra-stalk: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Associated-graded stalk chart of the total conormal algebra. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-graded-piece-stalk: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Stalk of each homogeneous conormal piece. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-piece-stalk: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Conormal stalk as the cotangent module of the actual kernel. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-conormal-zero-section-pullback: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns The relative-Spec conormal zero section pulls back by augmentation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-rees-associated-graded-chart: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Homogeneous chart for the extended Rees zero fibre. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-pur-rees-cone-normalized-existence: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Homogeneous-normalized Rees cone comparison exists. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-sfb-nodal-branch-double-cover: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns The two branches of a nodal family form an etale double cover of its singular subscheme. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-sfb-nodal-local-tangent-normalization: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns The tangent Proj of a geometric node is its quadratic normalization residue algebra. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-trf-nodal-point-finite-separable-splitting: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Splitting a nodal curve point over a finite separable field extension. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-augmented-module-complex-gluing: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Effective gluing of augmented module complexes. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-connected-torsor-module-descent: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Module descent on a connected finite torsor with natural geometric stalk comparisons. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-constant-module-locally-constant: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Natural locally constant model of the constant module sheaf. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-continuous-lattice-finite-coproduct: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Integral lattices assemble on finite disjoint unions. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-finite-ring-torsor-module-comparisons: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Pullback and unit comparisons for the associated module functor. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-finite-ring-torsor-module-descent: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Recovery of a torsor-trivialized finite-ring module sheaf. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-proetale-compatible-local-submodules: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Gluing compatible local submodules of an internal module. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-proetale-compatible-local-subsheaves: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Gluing compatible local subobjects of an abelian sheaf. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-proetale-local-quotient-vanishing: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Overlap compatibility annihilates the simultaneous local quotient map. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-proetale-local-subobject-kernel-effective: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Effectivity of the explicit kernel construction. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-site-module-compatible-tuples: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Compatible local module tuples satisfy the sheaf condition. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-site-module-sheaf-gluing: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Gluing module sheaf objects over a covering of a ringed site. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-site-module-sheaf-gluing-aux: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Compatible-tuples construction for module-sheaf gluing. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-associated-module-comparisons: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Pullback and coefficient comparisons. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-associated-module-essential-image: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Recovery of representations from constant torsor pullbacks. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-associated-module-full: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Fullness of the associated module functor. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-diagonal-evaluation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Diagonal evaluation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-diagonal-evaluation-bijective: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Objectwise bijectivity of graph evaluation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Surjectivity of diagonal evaluation of torsor sections. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-equivariant-module-is-sheaf: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Gluing equivariant module sections. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-equivariant-module-recover-linear: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Linear recovery for equivariant section transformations. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-equivariant-presheaf-sheaf: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Equivariant locally constant torsor functions form a sheaf. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-graph-evaluation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Graph evaluation is injective for equivariant locally constant functions. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-invariant-sections: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Invariant coefficient sections. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-module-descent-equivalence: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Additive module descent equivalence on a connected finite torsor. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-normalized-graph-evaluation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Ordinary normalized evaluation on a graph gives constant-sheaf coordinates. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-ordinary-evaluation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Ordinary natural normalized evaluation before deck equivariance. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-ordinary-evaluation-equivariant: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Deck equivariance forced by naturality and diagonal normalization. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-section-evaluation: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Existence of normalized torsor section evaluation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-section-evaluation-bijective: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Bijectivity of normalized torsor section evaluation. It does not supply this new comparison as stated.

lem-sfb-graph-cone-gluing vs lem-weil-pbc-torsor-section-evaluation-local: the new statement proves affine graph-ideal-power gluing and its agreement with the fixed exceptional fibre for arbitrary closed inclusions; the existing statement concerns Normalized evaluation on an etale object with a torsor section. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs def-sfb-nodal-branch-scheme: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns The graph-exceptional-fibre construction of the relative nodal branch scheme. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs def-trf-first-fitting-singular-subscheme: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns First Fitting singular subscheme of a morphism. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs def-trf-fitting-ideal-sheaf: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Fitting ideal sheaf of a finite-type quasi-coherent module. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs def-trf-fitting-ideal-zero: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Zeroth Fitting ideal of a finitely generated module. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-pur-conormal-algebra-flat-base-change: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Flat base change of the conormal algebra of a closed immersion. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-sfb-augmented-etale-associated-graded: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Infinitesimal neighbourhoods and associated graded rings under formally etale maps. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-sfb-dvr-nodal-chart-blowup-calculus: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Arithmetic nodal charts and their singular-point blowups. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-sfb-nodal-branch-double-cover: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns The two branches of a nodal family form an etale double cover of its singular subscheme. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-sfb-persistent-node-normalization: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Finite normalization at persistent nodes over an arbitrary trait. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-dth-fitting-smooth-locus: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns The dth Fitting ideal detects smoothness in a pure-dimensional flat family. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-fitting-ideal-direct-sum: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Zeroth Fitting ideal of a direct sum. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-fitting-ideal-independence-base-change: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Fitting ideals of a finite module: independence of generators and base change. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-formal-local-structure-nodal-family: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Formal local equation at a split node. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-nodal-etale-chart: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Etale normal forms for a nodal family with etale markings. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-nodal-family-etale-local-model: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Etale local model uv=h of an at-worst-nodal family of relative dimension one. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-nodal-family-fitting-singular: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Fitting singular subscheme of a nodal relative curve. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-nodal-generic-component-closure: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns A smooth generic component in a nodal neighbourhood has a flat closure and finite etale boundary. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-nodal-log-regularity: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Log regularity of a marked nodal curve over a log regular pair. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-ordered-nodal-branch-overlap: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Ordering nodal branches makes their vertical ideals agree generically on overlaps. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-valuation-smooth-branches-strict-chart: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Smooth fibre branches give a Zariski strict pair chart. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-chart vs lem-trf-valuation-symmetric-nodal-blowup: the new statement computes the entire graded graph cone and first-Fitting pullback in uv=h charts; the existing statement concerns Symmetric blowup along the closure of one nodal point. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs def-sfb-nodal-branch-scheme: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns The graph-exceptional-fibre construction of the relative nodal branch scheme. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-galois-fpqc-descend-open-immersion: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Being an open immersion descends along fpqc coverings (Stacks 02L3). It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-pur-conormal-algebra-flat-base-change: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Flat base change of the conormal algebra of a closed immersion. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-pur-conormal-algebra-homogeneous-ring-map: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Ring laws from homogeneous conormal representatives. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-pur-conormal-algebra-ring-adjoint: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Ring-sheaf adjoint from homogeneous formulas. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-sfb-dvr-nodal-chart-blowup-calculus: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Arithmetic nodal charts and their singular-point blowups. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-sfb-nodal-branch-double-cover: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns The two branches of a nodal family form an etale double cover of its singular subscheme. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-sfb-persistent-node-normalization: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Finite normalization at persistent nodes over an arbitrary trait. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-formal-local-structure-nodal-family: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Formal local equation at a split node. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-nodal-etale-chart: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Etale normal forms for a nodal family with etale markings. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-nodal-family-etale-local-model: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Etale local model uv=h of an at-worst-nodal family of relative dimension one. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-nodal-generic-component-closure: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns A smooth generic component in a nodal neighbourhood has a flat closure and finite etale boundary. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-nodal-log-regularity: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Log regularity of a marked nodal curve over a log regular pair. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-ordered-nodal-branch-overlap: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Ordering nodal branches makes their vertical ideals agree generically on overlaps. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-valuation-smooth-branches-strict-chart: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Smooth fibre branches give a Zariski strict pair chart. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-trf-valuation-symmetric-nodal-blowup: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Symmetric blowup along the closure of one nodal point. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-weil-pbc-fpqc-descend-affine: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Being affine descends along fpqc coverings (Stacks 02L5). It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-base-change vs lem-weil-pbc-fpqc-descend-isomorphism: the new statement proves arbitrary, potentially nonflat base change of that graded graph cone with representative formulas and composition laws; the existing statement concerns Being an isomorphism descends along flat surjective quasi-compact morphisms (Stacks 02L4). It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs def-sfb-nodal-branch-scheme: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns The graph-exceptional-fibre construction of the relative nodal branch scheme. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-sfb-nodal-branch-double-cover: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns The two branches of a nodal family form an etale double cover of its singular subscheme. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-sfb-nodal-local-tangent-normalization: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns The tangent Proj of a geometric node is its quadratic normalization residue algebra. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-geometric-fibre-unramified-criterion: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Unramifiedness tested on geometric fibres for a locally finite type morphism. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-nodal-curve-normalization-euler: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Euler characteristic of a nodal curve from its normalization. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-nodal-normalization-quotient: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Normalization quotient at split nodes. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-nodal-point-finite-separable-splitting: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Splitting a nodal curve point over a finite separable field extension. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-stacks-nodal-closed-subcurve: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Stacks lemma for a reduced closed subcurve of a nodal curve. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-unramified-field-fibre-decomposition: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Unramified schemes over a field are disjoint unions of finite separable spectra. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-trf-unramified-over-field-local-criterion: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns Local criterion for a locally finite type scheme to be unramified over a field. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-weil-pbc-unramified-algebra-over-field-product: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns An unramified algebra over a field is a finite product of finite separable extensions. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-weil-pbc-unramified-fibre-point-isolated: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns A point unramified in a locally finite type morphism is isolated in its fibre. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-weil-pbc-unramified-over-field-discrete: the new statement compares the graph local ring over the separable residue field with the original maximal-ideal filtration and assembles the normalization comparison over all singular points; the existing statement concerns A scheme unramified over a field is discrete. It does not supply this new comparison as stated.

lem-sfb-nodal-graph-cone-fibre vs lem-sfb-nodal-local-tangent-normalization: the existing node begins with gr_m of the original local ring; the new obligation first compares the fibre of the relative graph conormal with that ring, a separable diagonal-localization comparison not contained in the local normalization statement. The new node then applies that existing result and assembles over open singular points.

lem-sfb-graph-cone-gluing vs def-sfb-nodal-branch-scheme: the existing node gives the real blowup-exceptional-fibre definition; the new node proves that the algebra glued from the affine graph ideal powers realizes that particular construction, for arbitrary closed inclusions. It does not redefine the branch scheme.

## Review by Q38

I read Stacks curves.tex at remark-quadratic-extension (0CBT), remark-trivial-quadratic-extension (0CBU), lemma-split-node (0CBW), and lemma-etale-local-structure-nodal-family (0CBY). In divisors.tex I read definition-conormal-sheaf (0630), lemma-affine-conormal-sheaf (0633), lemma-conormal-algebra-functorial (0634) and lemma-conormal-algebra-functorial-flat (0635). These are the sources for the four new obligations: A carries the relative gluing argument, B the differential/Fitting and augmented-etale calculation, C the exceptional nonflat comparison and its coherence, D the graph-local comparison before applying 0CBT. The relative arguments are explicitly labelled agent extractions in source.place, not falsely attributed to a verbatim Stacks theorem.

Step 1 uses the full statements of nodal-family-fitting-singular and unramified-field-fibre-decomposition: the geometric hypotheses are identical, the former includes arbitrary base change, and the latter permits an arbitrary index set. Step 2 takes A's actual algebra construction and identification with the existing B_f, including isomorphism functoriality; no choice from an existence theorem is made. Step 3 takes B's entire graded chart and its covering assertion, then uses the flat clause of relative-proj-functoriality (etale is flat), the degree-localization description in affine-proj, degree-etale descent, etale-to-fpqc refinement and fpqc etale descent, and the rank statement of flf-properties. Each cited statement was opened; the elementary u/v localization calculation remains written in the parent.

Step 4 uses C's induced Proj isomorphisms and all its coherence laws, not a construction hidden in C's future proof. Step 5 uses D's graph-to-normalization identification, with k=kappa(t), and Step 4's fibre comparison. A field fibre is locally finite type and satisfies the same geometric-node and dimension hypotheses. Step 6 retains the original compactness argument: finite presentation includes quasi-compactness, closed-in-quasi-compact supplies compactness of D_t, the open-point covering is then finite, the decomposition theorem applies to the finite etale branch cover over each point, separable-permanence is applied to the two successive residue extensions, etale-coproduct supplies etaleness and finite-composition supplies finiteness. Step 7 uses closed-immersion-proper clause (b), the discrete-fibre characterization of quasi-finiteness in pqf-def-quasifinite and proper-quasifinite-finite, followed by finite-composition. All citations in these seven steps have the full verbatim statement in citations.json; thus the sheet contains the exact portion used and its surrounding hypotheses.

I checked B1-B10 and C1-C8 against the actual node files: every new statement introduces its objects and its comparison maps; notation is TeX with single escaping; notions are in stmt_deps; sources use tags and labels; no source-replacement route or SGA is used; the new nodes have no proof steps, no putative Mathlib match and all actual searches. The duplicate comparisons above distinguish the source-tag collisions rather than treating common tags as evidence of equivalence. The parent uses statements, never proofs, of its dependencies. None of A-D depends on the parent; their cross-links are statement definitions of G, not a cycle.

For E and small cases, I checked the empty singular scheme (all Proj and fibre claims are empty), an entirely smooth family, the split node over an arbitrary ring including nilpotents (positive graded pieces have basis u^n,v^n), a smoothing uv=h (h vanishes on D_U, not on the whole base), nonflat specialization h to zero (the specific monomial comparison survives), a nonsplit real node (a quadratic residue algebra rather than two rational points), and characteristic two (the etale split chart has two directions without dividing by two). No quasi-compactness is imposed until the finite-presentation conclusion; infinite disjoint nodal curves have an infinite disjoint singular scheme, handled by D. No total-space normalization or base-change-of-normalization claim was introduced. Nonseparated families use affine graph neighbourhoods. All new proof obligations have comparable original argument sizes: A=1616, B=2381, C=1711, D=1912 characters. The parent alone keeps the standard Proj/descent and finiteness assembly.

I also read Algebra 0H1D (lemma-formally-etale-lift-infinitesimal): its hypotheses are precisely the augmented formally-etale algebra comparison used in the old Steps 5 and 9, without an unjustified J=IC assumption. The preliminary local JSON inspection caught a notation token [b] incorrectly collected as a dependency; I removed it from C before the final dry run.

The sole return point is repaired by four new unsplit nodes and a parent proof under 3000 characters; nothing is repaired merely by shortening the old argument. The exact original arguments follow, with their destination, so every restriction, derivation, monomial, localization, descent and coherence argument remains available to the next worker. No mathematical correction to the item's statement was needed.

## Original arguments and their allocation

### Original step 1: retained in parent assembly

Apply [lem-trf-nodal-family-fitting-singular] with $S=T$: its hypotheses are exactly the flatness, local finite presentation and geometric-node assumptions here. Thus $|D|$ is the nonsmooth locus, $D\to T$ is unramified, and $D$ commutes with every base change. The same lemma applied to $f_t$ identifies $D_t$ with its first-Fitting singular scheme. By [lem-trf-unramified-field-fibre-decomposition], $D_t$ is a disjoint union of spectra of finite separable extensions of $\kappa(t)$, with no quasi-compactness assumption. In particular it is reduced and its points are exactly the nonsmooth points of $X_t$.

Source: literature/stacks-project/curves.tex — Tags 0C59 (lemma-nodal-family), 0C5B (lemma-base-change-nodal-family); Morphisms 02G7 (lemma-unramified-over-field).

Cited statements: lem-trf-nodal-family-fitting-singular, lem-trf-unramified-field-fibre-decomposition

### Original step 2: lem-sfb-graph-cone-gluing

Construct a graded algebra $\mathcal G_f$ on $D$ as follows. Choose affine $V\subset T$ and affine $U\subset f^{-1}(V)$, and put $D_U=D\cap U$. In $Y_U=U\times_V D_U$, the graph $s_U:D_U\to Y_U$ of $D_U\hookrightarrow U$ is closed: on rings its map is the surjection $\mathcal O(U)\otimes_{\mathcal O(V)}\mathcal O(D_U)\to\mathcal O(D_U)$, $b\otimes a\mapsto b|_{D_U}a$. Use its conormal algebra from [lem-pur-conormal-graded-algebra]. On a smaller affine open of $U$ the ambient graph neighbourhood is restricted in its first factor, so its ideal-power quotients restrict to the same quotients; restricting $V$ gives the same fibre product. These canonical identifications have identity and composition laws because they send every class of a section to its restriction. Apply [lem-weil-pbc-site-module-sheaf-gluing] on the Zariski site degree by degree. Multiplication and the unit agree locally, so the sheaf condition glues them uniquely. This gives a quasi-coherent graded algebra $\mathcal G_f$ on $D$, independent of all affine choices. This local construction does not require the global graph $D\to X\times_TD$ to be closed.

Source: literature/stacks-project/divisors.tex — Tags 0630 (definition-conormal-sheaf), 0633 (lemma-affine-conormal-sheaf), and Sites 04TR (lemma-glue-sheaves).

Cited statements: lem-pur-conormal-graded-algebra, lem-weil-pbc-site-module-sheaf-gluing

### Original step 3: lem-sfb-graph-cone-gluing

Define $B_f=\operatorname{Proj}_D(\mathcal G_f)$ with its structural morphism $p$. Existence and compatibility with the affine restrictions used above follow from [lemma-nagata-relative-proj-exists]. In particular this is a construction from actual ideal-power quotients; no normalization of the total space or choice of an ordering of branches occurs. The graded algebra and all its restriction maps are transported canonically by any isomorphism of families, and hence so is $B_f$.

Source: literature/stacks-project/constructions.tex — Relative Proj construction; realization of the tangent-cone construction (3) in Curves Tag 0CBT.

Cited statements: def-nagata-relative-proj, lemma-nagata-relative-proj-exists

### Original step 4: lem-sfb-nodal-graph-cone-chart

For a nodal chart [lem-trf-nodal-family-etale-local-model], write $W=\operatorname{Spec}_V\mathcal O_V[u,v]/(uv-h)$ and $U\to W$ etale. For any module $M$ over this coordinate ring, a derivation over $V$ is exactly a pair $(\alpha,\beta)\in M^2$ with $v\alpha+u\beta=0$: the values on $u,v$ determine it, and this equation makes it kill $uv-h$ and every multiple of that relation. Thus $\Omega_{W/V}$ has presentation $\mathcal O_W\xrightarrow{(v,u)}\mathcal O_W^2\to\Omega_{W/V}\to0$, and its first Fitting ideal is $(u,v)$. Apply this derivation comparison to both $U\to X$ and $V\to T$: the two base rings give the same differential module on $U$. Etale source maps preserve the computation. Indeed [lem-weil-pbc-flat-unramified-formally-etale] applied to the square-zero algebra $B\oplus M$ says precisely that each base derivation extends uniquely across an etale map; the representing differential modules are therefore related by tensor pullback. Fitting ideals commute with this tensor pullback by [lem-trf-fitting-ideal-independence-base-change]. Consequently the singular scheme in $U$ is $D_U=U\times_W V(h)$, where $V(h)\to W$ is $u=v=0$, and $D_U\to D$ is etale. These charts cover $D$; the etale pullbacks are justified by [lem-weil-pbc-etale-covering-base-change] (adding the identity chart when needed).

Source: literature/stacks-project/curves.tex — Tag 0CBY (lemma-etale-local-structure-nodal-family); Divisors 0C3I, More on Algebra 07ZA, and More on Morphisms 02HG/02HM infinitesimal criterion.

Cited statements: lem-trf-nodal-family-etale-local-model, lem-weil-pbc-flat-unramified-formally-etale, lem-trf-fitting-ideal-independence-base-change, def-trf-first-fitting-singular-subscheme, lem-weil-pbc-etale-covering-base-change

### Original step 5: lem-sfb-nodal-graph-cone-chart

Pull $\mathcal G_f$ to a singular chart $D_U$. This flat pullback commutes with conormal algebras by [lem-pur-conormal-algebra-flat-base-change]. Replacing $X$ near the graph by its etale neighbourhood $U$ does not change that algebra, by [lem-sfb-augmented-etale-associated-graded] on affine graph charts: the map of ambient rings is etale and both graph quotients are $\mathcal O(D_U)$. Apply the same lemma to the etale map $U\times_V D_U\to W\times_V D_U$, with the zero section on the right. On $D_U$ we have $h=0$. For any affine $\operatorname{Spec}A\subset D_U$, the right-hand augmented ring is $A[u,v]/(uv)$ with ideal $(u,v)$. Its degree-zero quotient is $A$, and its degree-$n$ quotient for $n>0$ is freely generated by $u^n,v^n$: its polynomial monomials with both exponents positive vanish, and the surviving monomials form an $A$-basis. Multiplication is the polynomial multiplication with $uv=0$. Hence
$$\mathcal G_f|_{D_U}\cong\mathcal O_{D_U}[u,v]/(uv),\qquad \deg u=\deg v=1.$$
Here the restriction denotes tensor pullback to the etale chart.

Source: literature/stacks-project/curves.tex — Tag 0CBY nodal charts; Algebra 0H1D (lemma-formally-etale-lift-infinitesimal); Divisors 0635 (lemma-conormal-algebra-functorial-flat).

Cited statements: lem-pur-conormal-algebra-flat-base-change, lem-sfb-augmented-etale-associated-graded

### Original step 6: retained in parent assembly

The two standard opens $D_+(u),D_+(v)$ of $\operatorname{Proj}A[u,v]/(uv)$ cover, by [def-nagata-affine-proj]. On $D_+(u)$, $u$ is inverted so $v=0$, and the degree-zero ring is $A$; similarly the ring on $D_+(v)$ is $A$. Their intersection is empty since $uv=0$ cannot be inverted in a nonzero ring. Since $D_U\to D$ is etale, hence flat, the flat base-change clause of [prop-nagata-relative-proj-functoriality] identifies $B_f\times_DD_U$ with $\operatorname{Proj}_{D_U}(\mathcal G_f|_{D_U})$. Thus $p$ pulls back to $D_U\amalg D_U\to D_U$ on the etale cover just obtained. By [lem-weil-pbc-finite-locally-free-degree-etale-descent], $p$ is finite locally free of degree two. By [lem-weil-pbc-fpqc-finer-than-etale] and [lem-galois-fpqc-descend-etale], it is etale. The rank-two assertion about $p_*\mathcal O_{B_f}$ is [lem-pc-flf-properties].

Source: literature/stacks-project/descent.tex — Tags 02VO (lemma-descending-property-finite-locally-free), 02VN (lemma-descending-property-etale); Topologies 022C; Proj standard affine charts.

Cited statements: def-nagata-affine-proj, prop-nagata-relative-proj-functoriality, lem-weil-pbc-finite-locally-free-degree-etale-descent, lem-weil-pbc-fpqc-finer-than-etale, lem-galois-fpqc-descend-etale, lem-pc-flf-properties

### Original step 7: lem-sfb-nodal-graph-cone-base-change

Let $a:T'\to T$ be arbitrary and identify $D'=D\times_TT'$ by Step 1. On graph ideals there is the canonical surjection $a_D^*\mathcal G_f\to\mathcal G_{f'}$ of [lem-pur-conormal-algebra-flat-base-change], which asserts surjectivity even without flatness. It induces a comparison
$$B_{f'}\longrightarrow B_f\times_DD'$$
by [prop-nagata-relative-proj-functoriality] and [lemma-nagata-relative-proj-base-change-arbitrary]. This comparison is an isomorphism: pull the original nodal charts to $D'$, which is an etale cover by [lem-weil-pbc-etale-covering-base-change], and apply Step 5 to both graphs. On an affine chart the graded map is exactly
$$A'\otimes_A A[u,v]/(uv)\longrightarrow A'[u,v]/(uv),\quad a'\otimes u\mapsto a'u,\quad a'\otimes v\mapsto a'v,$$
which is an isomorphism on the monomial bases in every degree. Thus its Proj map is an isomorphism there. To descend this assertion over an arbitrary affine open of $D'$, take a finite affine refinement of the etale covering; its disjoint union is flat, surjective and quasi-compact over that affine open. Apply [lem-weil-pbc-fpqc-descend-isomorphism] to the base-changed comparison (and its further base change to $B_f\times_DD'$). This proves the global comparison is an isomorphism without any flatness assumption on $a$.

Source: literature/stacks-project/divisors.tex — Tag 0635 canonical conormal comparison; Constructions relative Proj base change; Descent 02L4 (lemma-descending-property-isomorphism).

Cited statements: lem-pur-conormal-algebra-flat-base-change, prop-nagata-relative-proj-functoriality, lemma-nagata-relative-proj-base-change-arbitrary, lem-weil-pbc-fpqc-descend-isomorphism, lem-weil-pbc-etale-covering-base-change

### Original step 8: lem-sfb-nodal-graph-cone-base-change

For composable base changes all maps of graph ideal-power quotients send $[b]\otimes c$ to $[b\otimes c]$. Iterating this rule gives the same map as a single base change, under tensor associativity. The Proj comparisons are induced by these fixed graded maps; hence the isomorphisms of Step 7 satisfy the composition and identity compatibilities. The same formula shows their compatibility with family isomorphisms and with $p$.

Source: literature/stacks-project/divisors.tex — Tags 0634 (lemma-conormal-algebra-functorial), 0635; direct check on homogeneous representatives.

Cited statements: 

### Original step 9: lem-sfb-nodal-graph-cone-fibre

It remains to identify the fibre cover intrinsically with normalization branches. By Step 7 it suffices to work over $k=\kappa(t)$. By Step 1, $D_t$ is a disjoint union of $\operatorname{Spec}\kappa(x)$, with $\kappa(x)/k$ finite separable. Fix such a point and put $A=\mathcal O_{X_t,x}$, $\mathfrak m=\mathfrak m_x$, $\kappa=\kappa(x)$. The local ring at the graph point in $X_t\times_k\operatorname{Spec}\kappa$ is a localization of $A\otimes_k\kappa$. By [lem-weil-pbc-finite-separable-extension-etale], $\operatorname{Spec}\kappa\to\operatorname{Spec}k$ is etale and surjective; [lem-weil-pbc-etale-covering-base-change] makes $A\to A\otimes_k\kappa$ etale, so formally etale by [lem-weil-pbc-flat-unramified-formally-etale]. Localizing at the graph point preserves this: units modulo a square-zero ideal are units ($(1+n)^{-1}=1-n$), so the unique lift factors through the localization. Thus the map from $A$ is formally etale; its graph quotient is $\kappa$ and its inverse-image ideal is $\mathfrak m$. At this open point the graph conormal algebra is $\operatorname{gr}_J$ of that local ring ($J$ the graph ideal) by the stalk clause of [lem-pur-conormal-graded-algebra], and [lem-sfb-augmented-etale-associated-graded] identifies it with $\operatorname{gr}_{\mathfrak m}A$. Apply [lem-sfb-nodal-local-tangent-normalization]: its geometric node hypothesis is exactly our hypothesis on this fibre, and the separability hypothesis was verified above. It gives
$$B_f\times_D\operatorname{Spec}\kappa(x)\cong\operatorname{Spec}(A^\nu/\mathfrak m A^\nu)=X_t^\nu\times_{X_t}\operatorname{Spec}\kappa(x).$$
These canonical identifications on the disjoint open points of $D_t$ assemble to the asserted isomorphism over $D_t$, including infinitely many points. At an algebraically closed geometric point the quadratic algebra is $\Omega\times\Omega$ and its two points are exactly the two normalization branches.

Source: literature/stacks-project/curves.tex — Tags 0CBT (remark-quadratic-extension), 0CBU and 0CBW; Algebra formally etale localization and separable field maps.

Cited statements: lem-trf-unramified-field-fibre-decomposition, lem-sfb-augmented-etale-associated-graded, lem-sfb-nodal-local-tangent-normalization, def-weil-pbc-reduced-normalization, lem-weil-pbc-finite-separable-extension-etale, lem-weil-pbc-etale-covering-base-change, lem-weil-pbc-flat-unramified-formally-etale, lem-pur-conormal-graded-algebra

### Original step 10: retained in parent assembly

If $f$ is finitely presented then it is quasi-compact. Since $D\hookrightarrow X$ is closed, [lem-weil-pbc-closed-in-quasi-compact] makes $D_t$ quasi-compact. Its disjoint-open-point decomposition from Step 1 therefore has finitely many points. Each point is the spectrum of a finite separable field extension, so $D_t\to\operatorname{Spec}\kappa(t)$ is finite and is etale by [lem-exc-etale-coproduct-etale]. The same holds for $(B_f)_t$: it is a finite etale degree-two scheme over each of these finitely many separable field spectra, hence a finite disjoint union of finite separable field spectra over $\kappa(t)$. For this last description apply [lem-trf-unramified-field-fibre-decomposition] to each finite etale fibre over a field, and use [lem-zl-separable-permanence] for transitivity of separability and [lem-exc-etale-coproduct-etale] for etaleness. Finiteness also follows directly from [lem-weil-pbc-finite-composition]. This proves both fibre finiteness assertions.

Source: literature/stacks-project/curves.tex — Tags 0C59 and 0CBT; Morphisms 02G7 (lemma-unramified-over-field), quasi-compact discrete decomposition.

Cited statements: lem-trf-unramified-field-fibre-decomposition, def-sbc-locally-finite-presentation, def-weil-etale-morphism, lem-zl-separable-permanence, lem-exc-etale-coproduct-etale, lem-weil-pbc-closed-in-quasi-compact, lem-weil-pbc-finite-composition

### Original step 11: retained in parent assembly

Finally suppose $f$ is also proper. By [lem-weil-pbc-closed-immersion-proper], the closed subscheme $D$ is proper over $T$. Its fibres are finite by Step 10. They are discrete by Step 1, and properness includes finite type, so $D\to T$ is quasi-finite by [pqf-def-quasifinite]. Apply [cor-pqf-proper-quasifinite-finite] to obtain finiteness of $D\to T$. Since $p$ is finite, so is its composite $B_f\to T$ by [lem-weil-pbc-finite-composition].

Source: literature/stacks-project/curves.tex — Finiteness consequence of the nodal-family singular-scheme geometry; More on Morphisms proper quasi-finite finiteness and finite composition.

Cited statements: lem-weil-pbc-closed-immersion-proper, pqf-def-quasifinite, cor-pqf-proper-quasifinite-finite, lem-weil-pbc-finite-composition

## Unfinished work

The four statement-only nodes are intentionally unsplit for independent workers. No requested repair is left open. Delivery checks and final push follow this report.
