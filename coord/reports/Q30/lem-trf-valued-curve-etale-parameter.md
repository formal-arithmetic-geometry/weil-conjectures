# Worker report: lem-trf-valued-curve-etale-parameter

## Files written

All node paths below are under `dag/nodes/sec-trace-formula/` in this sandbox. The retained attempt already supplied the item, eight new statements, search logs and citations; this continuation preserved those files and reviewed their contents against the current repository.

- `lem-trf-valued-curve-etale-parameter.json`: existing statement, split into fourteen steps; original statement unchanged.
- `lem-trf-analytic-uniformization.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-valued-decompletion-etale.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-composed-valuation-etale.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-valuation-height-coarsening.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-sepclosed-rank-one-completion.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-curve-separating-parameters.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-curve-centred-valuation-dvr.json`: new statement, unsplit, no Mathlib match.
- `lem-trf-algclosed-curve-model.json`: new statement, unsplit, no Mathlib match.

`citations.json` records the verbatim statement used by every citation in every item step. `searches.jsonl` and `research/` retain the original searches and their returned signatures. No Lean, unit, chapter, coordinator or launcher file was changed. No compiler or build tool was run.

## Attachments

None. Searches of `WeilConjectures/` by the item tag, valued-parameter terminology, uniformization, decompletion, coarsening, separating bases and curve models found no project theorem giving the entire item. The upstream master's sorry declarations were not counted as proofs. Existing reduced-curve normalization is a different result, discussed below.

## Wanted literature

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Theorem 2.1.8 and its proof on printed pp. 12–13; Theorem 2.1.10 on p. 10; Propositions 2.2.1–2.2.2 on pp. 11–12; Lemma 2.1.4 on p. 8; Lemma 2.1.6 on p. 10; Proposition 4.3.3 on pp. 29–30, for this item and its Temkin children. The PDF is absent from the local literature archive. I read the primary PDF at https://arxiv.org/pdf/0707.3953v3 through the browser; no file was downloaded into the repository. The proof remains marked `proof_origin.by = agent`, as the brief requires for missing archival literature.

## Source error

Temkin's non-bounded paragraph, printed p. 12, asserts that any uniformizer at the smooth centre gives an étale coordinate. This inference fails over an imperfect separably closed field. Take such a field K of characteristic p, choose a outside K^p, put C = A¹_K and let c be the closed point (T^p-a). The element x = T^p-a is a uniformizer in K[T]_(T^p-a), but K(T)/K(x) is purely inseparable of degree p, so this coordinate cannot be étale. Instead the new centred-valuation node chooses an actual étale coordinate using Stacks 054L; the coordinate T itself works in the example. Its residue field need not equal K, and its coordinate need not be a uniformizer. What is needed is equality of the two residue fields of the étale local extension: their finite separable extension is also purely inseparable over the separably closed base, hence trivial. The item statement needs no correction.

The source's later use of the words “nowhere dense” for the bad-parameter subspace is stronger than needed. Step 7 proves density of its complement directly, using multiplication by powers of a small nonzero base element. This also works when that proper subspace is itself dense. No unit or chapter route was changed.

## Not duplicates

lem-trf-curve-centred-valuation-dvr vs sbc-thm-etale-local-normal-form: the existing 054L node gives étale affine-space charts for a smooth morphism; the new statement identifies a centred valuation with a curve local DVR, identifies the restricted rational valuation ring, and controls the residue extension. It does not duplicate the chart theorem.

lem-trf-curve-centred-valuation-dvr vs lem-sc-standard-smooth-local-relative-dimension: the existing 054L node supplies standard-smooth charts of a specified relative dimension; it does not state the centred valuation or restricted DVR identifications.

lem-trf-curve-centred-valuation-dvr vs lem-pc-dense-separable-points: the latter uses 054L to obtain density of separably rational closed points; the new statement concerns an arbitrary given valuation centre, including points with inseparable residue field.

lem-trf-curve-centred-valuation-dvr vs lem-weil-pbc-reduced-curve-normalization: both cite 0B8Y, but the existing result gives a finite smooth modification of a reduced curve over an algebraically closed field. The new result identifies a valuation already centred on a smooth curve over an arbitrary field and its étale parameter; no modification is asserted.

lem-trf-curve-separating-parameters vs lem-weil-pbc-geometrically-regular-finitely-generated-extensions: the existing 037X result concerns geometric regularity under finitely generated field extensions, not the existence and characterization of all separating rational parameters on a curve.

lem-trf-curve-separating-parameters vs lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra: the existing 037X node starts with a separable extension and constructs a smooth fraction-field model. The new statement goes from an existing smooth curve to separating parameters and identifies the entire bad-parameter subfield.

lem-trf-curve-separating-parameters vs new-smooth-fraction-field-localizations: the existing 037X node constructs localizations of a smooth fraction-field algebra; it does not give the separating-parameter criterion.

lem-trf-algclosed-curve-model vs lem-weil-pbc-reduced-curve-normalization: a smooth finite modification of a given reduced curve does not construct a proper model of an arbitrary one-variable field. Properness, with its centre-extension consequence, is the input needed by the induction here.

lem-trf-valuation-height-coarsening vs lem-trf-valuation-algebraic-height: the existing node treats algebraic extensions and prime-chain invariance; the new statement treats finite transcendence degree, compatible rank-one coarsenings in the bounded case, and residual composition.

lem-trf-valuation-height-coarsening vs lem-trf-abhyankar-inequality: the existing inequality bounds rational rank plus residue transcendence degree. The new node states the prime-chain/coarsening consequences and the compatible residual valuation description, not the inequality.

The whole DAG was searched for the source tags 054L, 0B8Y, 037X, 0BY1, 0BY3 and the valuation/completion/parameter terminology. Blueprint searches for analytic field, coarsening, composed valuation, decompletion, separating parameter, smooth curve valuation and uniformization found no equivalent node; projective-model and separating searches returned unrelated categorical-trace, duality-local-model and Nagata-separation nodes. The nearest imported ancestor remains lem-trf-local-term-locality, with the retained via chain. The unit and chapter records were read and left intact: this item is not the unit's key node.

The first delivery dry run also classified the arXiv identifier prefix `0707` as a common Stacks tag. I opened every flagged node; their actual statements are distinguished below. These additional lines satisfy the requested duplicate review without changing the source identifiers or the checker.

lem-trf-analytic-uniformization vs lem-trf-valued-curve-etale-parameter: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the item concerns an algebraic one-variable extension over a possibly higher-height separably closed valued field; the new result is a separate input to its fourteen-step induction and does not state its conclusion under its hypotheses.

lem-trf-analytic-uniformization vs def-trf-birational-quasi-modification: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines a class of scheme morphisms using integrality, birationality and finite-type conditions.

lem-trf-analytic-uniformization vs def-trf-centred-valuation: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node only defines compatibility of a valuation-centre morphism with the generic point.

lem-trf-analytic-uniformization vs def-trf-local-marking-length: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines a local vector-space length of the marking on a multipointed curve.

lem-trf-analytic-uniformization vs def-trf-modification: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines proper modifications and their generic base-change condition.

lem-trf-analytic-uniformization vs def-trf-multipointed-curve-modification: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines morphisms, semistability and stability of marked curve modifications.

lem-trf-analytic-uniformization vs def-trf-multipointed-curve: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines a flat finitely presented curve and its closed marking.

lem-trf-analytic-uniformization vs def-trf-multipointed-eta-modification: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines proper pair modifications that become isomorphisms after the specified base change.

lem-trf-analytic-uniformization vs def-trf-nodal-dualizing-datum: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines Jacobian-normalized dualizing data on nodal curve charts.

lem-trf-analytic-uniformization vs def-trf-projective-line-tree: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines the component and node conditions for a projective-line tree.

lem-trf-analytic-uniformization vs def-trf-rational-rank: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines the dimension of the rationalization of an abelian group.

lem-trf-analytic-uniformization vs def-trf-schematically-dense-open: the new statement constructs a rational analytic parameter with an etale completed extension and perturbation/residue control; the existing node defines schematic density through injectivity of restriction on structure-sheaf sections.

lem-trf-composed-valuation-etale vs lem-trf-valued-curve-etale-parameter: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the item concerns an algebraic one-variable extension over a possibly higher-height separably closed valued field; the new result is a separate input to its fourteen-step induction and does not state its conclusion under its hypotheses.

lem-trf-composed-valuation-etale vs def-trf-birational-quasi-modification: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines a class of scheme morphisms using integrality, birationality and finite-type conditions.

lem-trf-composed-valuation-etale vs def-trf-centred-valuation: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node only defines compatibility of a valuation-centre morphism with the generic point.

lem-trf-composed-valuation-etale vs def-trf-local-marking-length: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines a local vector-space length of the marking on a multipointed curve.

lem-trf-composed-valuation-etale vs def-trf-modification: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines proper modifications and their generic base-change condition.

lem-trf-composed-valuation-etale vs def-trf-multipointed-curve-modification: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines morphisms, semistability and stability of marked curve modifications.

lem-trf-composed-valuation-etale vs def-trf-multipointed-curve: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines a flat finitely presented curve and its closed marking.

lem-trf-composed-valuation-etale vs def-trf-multipointed-eta-modification: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines proper pair modifications that become isomorphisms after the specified base change.

lem-trf-composed-valuation-etale vs def-trf-nodal-dualizing-datum: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines Jacobian-normalized dualizing data on nodal curve charts.

lem-trf-composed-valuation-etale vs def-trf-projective-line-tree: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines the component and node conditions for a projective-line tree.

lem-trf-composed-valuation-etale vs def-trf-rational-rank: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines the dimension of the rationalization of an abelian group.

lem-trf-composed-valuation-etale vs def-trf-schematically-dense-open: the new statement proves that etaleness of coarsened and residual valuation extensions gives etaleness of the composed inverse-image rings; the existing node defines schematic density through injectivity of restriction on structure-sheaf sections.

lem-trf-curve-separating-parameters vs lem-trf-valued-curve-etale-parameter: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the item concerns an algebraic one-variable extension over a possibly higher-height separably closed valued field; the new result is a separate input to its fourteen-step induction and does not state its conclusion under its hypotheses.

lem-trf-curve-separating-parameters vs def-trf-birational-quasi-modification: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines a class of scheme morphisms using integrality, birationality and finite-type conditions.

lem-trf-curve-separating-parameters vs def-trf-centred-valuation: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node only defines compatibility of a valuation-centre morphism with the generic point.

lem-trf-curve-separating-parameters vs def-trf-local-marking-length: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines a local vector-space length of the marking on a multipointed curve.

lem-trf-curve-separating-parameters vs def-trf-modification: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines proper modifications and their generic base-change condition.

lem-trf-curve-separating-parameters vs def-trf-multipointed-curve-modification: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines morphisms, semistability and stability of marked curve modifications.

lem-trf-curve-separating-parameters vs def-trf-multipointed-curve: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines a flat finitely presented curve and its closed marking.

lem-trf-curve-separating-parameters vs def-trf-multipointed-eta-modification: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines proper pair modifications that become isomorphisms after the specified base change.

lem-trf-curve-separating-parameters vs def-trf-nodal-dualizing-datum: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines Jacobian-normalized dualizing data on nodal curve charts.

lem-trf-curve-separating-parameters vs def-trf-projective-line-tree: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines the component and node conditions for a projective-line tree.

lem-trf-curve-separating-parameters vs def-trf-rational-rank: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines the dimension of the rationalization of an abelian group.

lem-trf-curve-separating-parameters vs def-trf-schematically-dense-open: the new statement characterizes separating parameters of a smooth function field by the proper bad-parameter subfield; the existing node defines schematic density through injectivity of restriction on structure-sheaf sections.

lem-trf-sepclosed-rank-one-completion vs lem-trf-valued-curve-etale-parameter: the new statement asserts algebraic closure of a rank-one completion and its residue field; the item concerns an algebraic one-variable extension over a possibly higher-height separably closed valued field; the new result is a separate input to its fourteen-step induction and does not state its conclusion under its hypotheses.

lem-trf-sepclosed-rank-one-completion vs def-trf-birational-quasi-modification: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines a class of scheme morphisms using integrality, birationality and finite-type conditions.

lem-trf-sepclosed-rank-one-completion vs def-trf-centred-valuation: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node only defines compatibility of a valuation-centre morphism with the generic point.

lem-trf-sepclosed-rank-one-completion vs def-trf-local-marking-length: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines a local vector-space length of the marking on a multipointed curve.

lem-trf-sepclosed-rank-one-completion vs def-trf-modification: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines proper modifications and their generic base-change condition.

lem-trf-sepclosed-rank-one-completion vs def-trf-multipointed-curve-modification: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines morphisms, semistability and stability of marked curve modifications.

lem-trf-sepclosed-rank-one-completion vs def-trf-multipointed-curve: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines a flat finitely presented curve and its closed marking.

lem-trf-sepclosed-rank-one-completion vs def-trf-multipointed-eta-modification: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines proper pair modifications that become isomorphisms after the specified base change.

lem-trf-sepclosed-rank-one-completion vs def-trf-nodal-dualizing-datum: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines Jacobian-normalized dualizing data on nodal curve charts.

lem-trf-sepclosed-rank-one-completion vs def-trf-projective-line-tree: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines the component and node conditions for a projective-line tree.

lem-trf-sepclosed-rank-one-completion vs def-trf-rational-rank: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines the dimension of the rationalization of an abelian group.

lem-trf-sepclosed-rank-one-completion vs def-trf-schematically-dense-open: the new statement asserts algebraic closure of a rank-one completion and its residue field; the existing node defines schematic density through injectivity of restriction on structure-sheaf sections.

lem-trf-valuation-height-coarsening vs lem-trf-valued-curve-etale-parameter: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the item concerns an algebraic one-variable extension over a possibly higher-height separably closed valued field; the new result is a separate input to its fourteen-step induction and does not state its conclusion under its hypotheses.

lem-trf-valuation-height-coarsening vs def-trf-birational-quasi-modification: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines a class of scheme morphisms using integrality, birationality and finite-type conditions.

lem-trf-valuation-height-coarsening vs def-trf-centred-valuation: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node only defines compatibility of a valuation-centre morphism with the generic point.

lem-trf-valuation-height-coarsening vs def-trf-local-marking-length: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines a local vector-space length of the marking on a multipointed curve.

lem-trf-valuation-height-coarsening vs def-trf-modification: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines proper modifications and their generic base-change condition.

lem-trf-valuation-height-coarsening vs def-trf-multipointed-curve-modification: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines morphisms, semistability and stability of marked curve modifications.

lem-trf-valuation-height-coarsening vs def-trf-multipointed-curve: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines a flat finitely presented curve and its closed marking.

lem-trf-valuation-height-coarsening vs def-trf-multipointed-eta-modification: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines proper pair modifications that become isomorphisms after the specified base change.

lem-trf-valuation-height-coarsening vs def-trf-nodal-dualizing-datum: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines Jacobian-normalized dualizing data on nodal curve charts.

lem-trf-valuation-height-coarsening vs def-trf-projective-line-tree: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines the component and node conditions for a projective-line tree.

lem-trf-valuation-height-coarsening vs def-trf-rational-rank: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines the dimension of the rationalization of an abelian group.

lem-trf-valuation-height-coarsening vs def-trf-schematically-dense-open: the new statement gives finite height, compatible rank-one coarsenings and residual inverse-image descriptions; the existing node defines schematic density through injectivity of restriction on structure-sheaf sections.

lem-trf-valued-decompletion-etale vs lem-trf-valued-curve-etale-parameter: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the item concerns an algebraic one-variable extension over a possibly higher-height separably closed valued field; the new result is a separate input to its fourteen-step induction and does not state its conclusion under its hypotheses.

lem-trf-valued-decompletion-etale vs def-trf-birational-quasi-modification: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines a class of scheme morphisms using integrality, birationality and finite-type conditions.

lem-trf-valued-decompletion-etale vs def-trf-centred-valuation: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node only defines compatibility of a valuation-centre morphism with the generic point.

lem-trf-valued-decompletion-etale vs def-trf-local-marking-length: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines a local vector-space length of the marking on a multipointed curve.

lem-trf-valued-decompletion-etale vs def-trf-modification: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines proper modifications and their generic base-change condition.

lem-trf-valued-decompletion-etale vs def-trf-multipointed-curve-modification: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines morphisms, semistability and stability of marked curve modifications.

lem-trf-valued-decompletion-etale vs def-trf-multipointed-curve: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines a flat finitely presented curve and its closed marking.

lem-trf-valued-decompletion-etale vs def-trf-multipointed-eta-modification: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines proper pair modifications that become isomorphisms after the specified base change.

lem-trf-valued-decompletion-etale vs def-trf-nodal-dualizing-datum: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines Jacobian-normalized dualizing data on nodal curve charts.

lem-trf-valued-decompletion-etale vs def-trf-projective-line-tree: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines the component and node conditions for a projective-line tree.

lem-trf-valued-decompletion-etale vs def-trf-rational-rank: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines the dimension of the rationalization of an abelian group.

lem-trf-valued-decompletion-etale vs def-trf-schematically-dense-open: the new statement compares etaleness of rank-one valuation ring extensions with their completed extensions, retaining field separability; the existing node defines schematic density through injectivity of restriction on structure-sheaf sections.

A new concurrent repository node appeared between dry run and push, also flagged through the arXiv prefix. I read its definition and added these comparisons before repeating the dry run.

lem-trf-analytic-uniformization vs def-trf-adic-ring-completion-map: the new statement produces an analytic rational parameter and controls its perturbations; the existing node only defines a coordinatewise functorial map on principal ideal-adic completions of arbitrary commutative rings. It has no valued-field uniformization or etaleness assertion.

lem-trf-composed-valuation-etale vs def-trf-adic-ring-completion-map: the new statement proves an etale composition criterion for coarsened and residual valuations; the existing node only defines a coordinatewise functorial map on principal ideal-adic completions of arbitrary commutative rings. It has no valued-field uniformization or etaleness assertion.

lem-trf-curve-separating-parameters vs def-trf-adic-ring-completion-map: the new statement characterizes separating parameters and the bad-parameter subfield; the existing node only defines a coordinatewise functorial map on principal ideal-adic completions of arbitrary commutative rings. It has no valued-field uniformization or etaleness assertion.

lem-trf-sepclosed-rank-one-completion vs def-trf-adic-ring-completion-map: the new statement proves algebraic closure and residue-field invariance for a rank-one separably closed field; the existing node only defines a coordinatewise functorial map on principal ideal-adic completions of arbitrary commutative rings. It has no valued-field uniformization or etaleness assertion.

lem-trf-valuation-height-coarsening vs def-trf-adic-ring-completion-map: the new statement asserts finite-height bounds and compatible residual coarsenings; the existing node only defines a coordinatewise functorial map on principal ideal-adic completions of arbitrary commutative rings. It has no valued-field uniformization or etaleness assertion.

lem-trf-valued-decompletion-etale vs def-trf-adic-ring-completion-map: the new statement compares etaleness before and after metric completion of a finite rank-one field extension; the existing node only defines a coordinatewise functorial map on principal ideal-adic completions of arbitrary commutative rings. It has no valued-field uniformization or etaleness assertion.

After the next shared fetch, the checker flagged ordinary-multiple-point through the same arXiv prefix. I also read the remaining Temkin-source definition nodes currently in the repository, to make the duplicate review robust to concurrent changes.

lem-trf-analytic-uniformization vs def-trf-ordinary-multiple-point: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines a split ordinary multiple point by a scalar-compatible isomorphism of its completed local ring with a union of coordinate axes, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-valuation-comap-residue: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines the canonical field embedding on residue fields for the restriction of a valuation along a field embedding, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-restricted-series-presentation: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines restricted power series, topologically finite presentations, affinoid quotient presentations and bounded generating images, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-semistable-multipointed-curve: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines semistability by the marking and geometric-fibre nodal conditions, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-strictly-semistable-curve: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines flat relative curves with smooth or nodal etale charts, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-semistable-multipointed-pair: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines underlying marked pairs, their base change, semistability and geometric stability, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-stable-multipointed-eta-modification: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines stable proper generic modifications by the absence of contracted exceptional projective-line components, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-semistable-marked-point: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines semistability at a point by restriction of the marked pair to an open neighbourhood, with no assertion of this valued-field theorem.

lem-trf-analytic-uniformization vs def-trf-strict-semistable-curve: the new result produces an analytic rational parameter and controls its perturbations; the existing node defines flat relative curves admitting smooth or nodal etale local charts, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-ordinary-multiple-point: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines a split ordinary multiple point by a scalar-compatible isomorphism of its completed local ring with a union of coordinate axes, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-valuation-comap-residue: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines the canonical field embedding on residue fields for the restriction of a valuation along a field embedding, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-restricted-series-presentation: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines restricted power series, topologically finite presentations, affinoid quotient presentations and bounded generating images, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-semistable-multipointed-curve: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines semistability by the marking and geometric-fibre nodal conditions, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-strictly-semistable-curve: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines flat relative curves with smooth or nodal etale charts, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-semistable-multipointed-pair: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines underlying marked pairs, their base change, semistability and geometric stability, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-stable-multipointed-eta-modification: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines stable proper generic modifications by the absence of contracted exceptional projective-line components, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-semistable-marked-point: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines semistability at a point by restriction of the marked pair to an open neighbourhood, with no assertion of this valued-field theorem.

lem-trf-composed-valuation-etale vs def-trf-strict-semistable-curve: the new result proves an etale composition criterion for coarsened and residual valuations; the existing node defines flat relative curves admitting smooth or nodal etale local charts, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-ordinary-multiple-point: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines a split ordinary multiple point by a scalar-compatible isomorphism of its completed local ring with a union of coordinate axes, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-valuation-comap-residue: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines the canonical field embedding on residue fields for the restriction of a valuation along a field embedding, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-restricted-series-presentation: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines restricted power series, topologically finite presentations, affinoid quotient presentations and bounded generating images, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-semistable-multipointed-curve: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines semistability by the marking and geometric-fibre nodal conditions, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-strictly-semistable-curve: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines flat relative curves with smooth or nodal etale charts, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-semistable-multipointed-pair: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines underlying marked pairs, their base change, semistability and geometric stability, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-stable-multipointed-eta-modification: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines stable proper generic modifications by the absence of contracted exceptional projective-line components, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-semistable-marked-point: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines semistability at a point by restriction of the marked pair to an open neighbourhood, with no assertion of this valued-field theorem.

lem-trf-curve-separating-parameters vs def-trf-strict-semistable-curve: the new result characterizes separating parameters and the bad-parameter subfield; the existing node defines flat relative curves admitting smooth or nodal etale local charts, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-ordinary-multiple-point: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines a split ordinary multiple point by a scalar-compatible isomorphism of its completed local ring with a union of coordinate axes, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-valuation-comap-residue: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines the canonical field embedding on residue fields for the restriction of a valuation along a field embedding, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-restricted-series-presentation: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines restricted power series, topologically finite presentations, affinoid quotient presentations and bounded generating images, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-semistable-multipointed-curve: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines semistability by the marking and geometric-fibre nodal conditions, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-strictly-semistable-curve: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines flat relative curves with smooth or nodal etale charts, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-semistable-multipointed-pair: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines underlying marked pairs, their base change, semistability and geometric stability, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-stable-multipointed-eta-modification: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines stable proper generic modifications by the absence of contracted exceptional projective-line components, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-semistable-marked-point: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines semistability at a point by restriction of the marked pair to an open neighbourhood, with no assertion of this valued-field theorem.

lem-trf-sepclosed-rank-one-completion vs def-trf-strict-semistable-curve: the new result proves algebraic closure and residue invariance for a rank-one separably closed field; the existing node defines flat relative curves admitting smooth or nodal etale local charts, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-ordinary-multiple-point: the new result gives height bounds and compatible residual coarsenings; the existing node defines a split ordinary multiple point by a scalar-compatible isomorphism of its completed local ring with a union of coordinate axes, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-valuation-comap-residue: the new result gives height bounds and compatible residual coarsenings; the existing node defines the canonical field embedding on residue fields for the restriction of a valuation along a field embedding, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-restricted-series-presentation: the new result gives height bounds and compatible residual coarsenings; the existing node defines restricted power series, topologically finite presentations, affinoid quotient presentations and bounded generating images, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-semistable-multipointed-curve: the new result gives height bounds and compatible residual coarsenings; the existing node defines semistability by the marking and geometric-fibre nodal conditions, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-strictly-semistable-curve: the new result gives height bounds and compatible residual coarsenings; the existing node defines flat relative curves with smooth or nodal etale charts, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-semistable-multipointed-pair: the new result gives height bounds and compatible residual coarsenings; the existing node defines underlying marked pairs, their base change, semistability and geometric stability, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-stable-multipointed-eta-modification: the new result gives height bounds and compatible residual coarsenings; the existing node defines stable proper generic modifications by the absence of contracted exceptional projective-line components, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-semistable-marked-point: the new result gives height bounds and compatible residual coarsenings; the existing node defines semistability at a point by restriction of the marked pair to an open neighbourhood, with no assertion of this valued-field theorem.

lem-trf-valuation-height-coarsening vs def-trf-strict-semistable-curve: the new result gives height bounds and compatible residual coarsenings; the existing node defines flat relative curves admitting smooth or nodal etale local charts, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-ordinary-multiple-point: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines a split ordinary multiple point by a scalar-compatible isomorphism of its completed local ring with a union of coordinate axes, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-valuation-comap-residue: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines the canonical field embedding on residue fields for the restriction of a valuation along a field embedding, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-restricted-series-presentation: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines restricted power series, topologically finite presentations, affinoid quotient presentations and bounded generating images, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-semistable-multipointed-curve: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines semistability by the marking and geometric-fibre nodal conditions, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-strictly-semistable-curve: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines flat relative curves with smooth or nodal etale charts, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-semistable-multipointed-pair: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines underlying marked pairs, their base change, semistability and geometric stability, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-stable-multipointed-eta-modification: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines stable proper generic modifications by the absence of contracted exceptional projective-line components, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-semistable-marked-point: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines semistability at a point by restriction of the marked pair to an open neighbourhood, with no assertion of this valued-field theorem.

lem-trf-valued-decompletion-etale vs def-trf-strict-semistable-curve: the new result compares etaleness before and after metric completion of a finite rank-one extension; the existing node defines flat relative curves admitting smooth or nodal etale local charts, with no assertion of this valued-field theorem.

## Mathlib search review

I read the retained search outputs before reusing them. All eight new nodes have natural-language LeanSearch, two differently phrased LeanFinder searches, Loogle and source grep. These are genuine recorded calls in searches.jsonl, not proposed searches. None gives the entire corresponding statement or a one-line specialization of it.

For analytic uniformization, the hits supply completions, spectral norms or number-field infinite-place unramifiedness, not the analytic parameter theorem. For decompletion, field étaleness/separability and number-field completion lemmas do not compare general rank-one valuation rings. For valuation composition, `Algebra.Etale.comp` concerns a tower of algebra maps, not the inverse-image rings of residual valuations. For height/coarsening, `ValuationSubring.primeSpectrumOrderEquiv` supplies only part of the statement; I read its source around lines 264–390. It does not prove the height bound or compatible rank-one assertion. For separably closed completion, `IsAlgClosed.of_denseRange` and the PadicComplex instance require algebraic closure of the dense source; separable closure of the source alone is the substantive missing input. For separating parameters, perfect-field existence and smoothness from a chosen separating basis do not characterize the bad subfield over an imperfect separably closed field. For centred valuation DVRs, the DVR-to-valuation-ring facts omit the curve chart and restricted field identifications. For proper curve models, function-field definitions and Weierstrass models do not construct the required proper model of an arbitrary one-variable field.

One retained Loogle query used the nonexistent identifier IsTranscendental. I preserved its actual output, corrected its verdict to unavailable for that invalid query, and ran `Algebra.IsSeparable, AlgebraicIndependent` instead. Its sole hit, `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable`, proves formal smoothness from already chosen independent generators and separability; it does not state the new node. All successful old queries remain recorded unchanged.

lem-trf-analytic-uniformization vs def-trf-birational-valuation-neighbourhood-data: the new theorem constructs analytic parameters giving finite etale completed extensions, with perturbation and prescribed-residue control; the existing node defines valuation cylinders, their topology, affine neighbourhood systems and their colimit data on birational models. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-analytic-uniformization vs def-trf-horizontal-valuation-curve-data: the new theorem constructs analytic parameters giving finite etale completed extensions, with perturbation and prescribed-residue control; the existing node defines finite-height valuation bases, relative curves and schematic-closure pair data. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-composed-valuation-etale vs def-trf-birational-valuation-neighbourhood-data: the new theorem asserts etaleness of composed valuation-ring extensions from coarsened and residual etaleness; the existing node defines valuation cylinders, their topology, affine neighbourhood systems and their colimit data on birational models. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-composed-valuation-etale vs def-trf-horizontal-valuation-curve-data: the new theorem asserts etaleness of composed valuation-ring extensions from coarsened and residual etaleness; the existing node defines finite-height valuation bases, relative curves and schematic-closure pair data. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-curve-separating-parameters vs def-trf-birational-valuation-neighbourhood-data: the new theorem characterizes separating rational parameters by the proper bad-parameter subfield; the existing node defines valuation cylinders, their topology, affine neighbourhood systems and their colimit data on birational models. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-curve-separating-parameters vs def-trf-horizontal-valuation-curve-data: the new theorem characterizes separating rational parameters by the proper bad-parameter subfield; the existing node defines finite-height valuation bases, relative curves and schematic-closure pair data. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-sepclosed-rank-one-completion vs def-trf-birational-valuation-neighbourhood-data: the new theorem asserts algebraic closedness of the rank-one completion and its residue field; the existing node defines valuation cylinders, their topology, affine neighbourhood systems and their colimit data on birational models. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-sepclosed-rank-one-completion vs def-trf-horizontal-valuation-curve-data: the new theorem asserts algebraic closedness of the rank-one completion and its residue field; the existing node defines finite-height valuation bases, relative curves and schematic-closure pair data. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-valuation-height-coarsening vs def-trf-birational-valuation-neighbourhood-data: the new theorem asserts finite-height bounds and compatible rank-one coarsenings with residual composition; the existing node defines valuation cylinders, their topology, affine neighbourhood systems and their colimit data on birational models. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-valuation-height-coarsening vs def-trf-horizontal-valuation-curve-data: the new theorem asserts finite-height bounds and compatible rank-one coarsenings with residual composition; the existing node defines finite-height valuation bases, relative curves and schematic-closure pair data. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-valued-decompletion-etale vs def-trf-birational-valuation-neighbourhood-data: the new theorem compares etaleness before and after rank-one completion of a finite separable field extension; the existing node defines valuation cylinders, their topology, affine neighbourhood systems and their colimit data on birational models. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

lem-trf-valued-decompletion-etale vs def-trf-horizontal-valuation-curve-data: the new theorem compares etaleness before and after rank-one completion of a finite separable field extension; the existing node defines finite-height valuation bases, relative curves and schematic-closure pair data. The shared string 0707 comes from the arXiv filename, not a common mathematical assertion.

## Review by Q30

I read the item, all eight new statements, every existing statement cited by its proof, the unit and chapter, and delivery-errors B–E. I compared the retained item with the current repository: the original natural-language statement is preserved and remains unsplit in the repository. The retained attempt had no report, so the continuation began by reviewing it; the permitted server review_split check passed before this report was written.

For the item I read Temkin Theorem 2.1.8, its finite-height proof, and the analytic and valuative inputs in §§2.1–2.2 through the primary PDF. The finite-height hypothesis is already part of this item, so the proof starts with finite-height induction and does not use the paper's preliminary descent from infinite height. The smooth-centre assumption is used in the non-bounded case, not dropped.

For each new source I checked the actual assertion. Analytic uniformization uses Theorem 2.1.10(i)–(iii) and Lemma 2.1.6 to express unramifiedness as étaleness of valuation rings. I made the perturbation clause jointly existential in x and epsilon, precisely the assertion used. Decompletion is Proposition 2.2.1. I moved finiteness of E/F into its opening hypotheses so it governs both the degree/residue assertions and the equivalence, with separability explicitly retained, and the completion/residue properties used in its proof. Composition is Proposition 2.2.2 with finite heights and finite field extension retained. Coarsening is the §2.1 composition description and Lemma 2.1.4, together with the height bound and the compatible rank-one choice used in the theorem's proof. Algebraic closure of completion/residue is the explicit input at the start of the height-one argument on p. 13; it is not assumed merely from residue separable closure. Separating parameters use the criterion stated in that same proof, including the characteristic-zero convention and properness of the bad subfield. The centred-valuation node uses the actual chart assertion in morphisms.tex, label lemma-smooth-etale-over-affine-space (054L), and varieties.tex, label lemma-regular-point-on-curve (0B8Y), with the repaired coordinate explained above. For proper models I read curves.tex, theorem-curves-rational-maps (0BY1) and lemma-nonsingular-model-smooth (0BY3): algebraically closed implies perfect, so the normal proper model is smooth; its last clause is the valuative criterion of properness. All these children remain statement-only; their sources are not disguised proofs in their statements.

Step 1 uses the exact separating-parameter and height/coarsening statements to set up uniform induction, and existing algebraic-height invariance to give finite height of restricted rational valuations. Step 2 uses existing étale base change, étale algebras over fields, and open-immersion/composition statements. The finite-prime argument is written out: finitely many fibres with finitely many points give finitely many primes, a finite product removes exactly the primes not below the chosen prime, and the resulting principal open is its local spectrum. This is an elementary step from those cited statements, so I did not retain a separate node for it.

Steps 3–4 use the full centred-valuation statement, including equality of residue fields, then the inverse-image and restriction clauses of coarsening and the composed-valuation criterion. The chosen coordinate comes from an étale chart; no arbitrary uniformizer is substituted. In Step 5, height zero and KW=L force W=L, and the existing finite-separable-field étaleness statement applies to the chosen separating parameter. This explicitly handles the trivial base valuation.

Step 6 uses compatible coarsening, the existing height-one real-absolute-value theorem, and the new separably-closed completion input. Both restricted absolute values are nontrivial because both coarsenings have height one. Step 7 is elementary: a proper K-linear subspace misses every b*c^n with b outside it, giving complement density; it relies on the properties established in Steps 1 and 6. Step 8 uses the completion degree bound for a finite extension and coefficientwise approximation of rational functions to identify the two closures. It checks the analytic theorem's topological finite-generation hypothesis rather than simply assuming it.

Step 9 separates the case of equal completed fields from the genuine analytic extension, uses perturbation density to retain algebraic separability, then applies decompletion and composition. The residual valuation extension is the identity because E=k and W restricts to R. Step 10 uses the existing Abhyankar inequality only for its residue-transcendence bound. Algebraic closedness of k excludes a nontrivial algebraic residue extension. I checked the coefficient-normalization argument for the residue of K(y), and the lift-of-independent-residues argument bounding [E:k(ybar)] by [L:K(y)]. Thus the residual field really is finitely generated before invoking induction.

Step 11 uses the proper-model statement to supply a smooth centre for the residual extension, checks the base height is h−1 and the residual restriction is R0, and invokes the induction hypothesis only at that smaller height. Existing étale base change and étale-field-algebra classification prove residual separability. I expanded the generic-fibre identification: after base change to the source fraction field the ring is an algebraic domain over a field, hence a field, and its fraction field is E. Step 12 chooses a separating lift in its residue ball, uses preservation of residue fields, checks the finite separable residue-extension clause of analytic uniformization, and then uses decompletion. Step 13 uses the restriction clause and algebraic-height invariance to check all residual finite-height hypotheses before composition. Step 14 is the elementary inversion argument: a nonzero transcendental parameter or its inverse is integral, with exactly the same rational subfield and the same ring extension.

I tested the new statements on L=K(T), a trivial valuation, a closed-point DVR, height one, identical residual fields, a transcendental Gauss residue and a composite higher-height valuation. The centred node explicitly excludes A=L; the induction treats that case separately. The residue-prescribed analytic clause assumes a nonconstant residue, so it does not make a claim in the immediate-extension case. The completion criterion retains separability to exclude purely inseparable examples. The algebraically closed hypothesis in the proper-model node prevents the invalid assertion that every regular curve over an imperfect field is smooth. The concrete imperfect-field example above tests the coordinate repair. All item steps are shorter than 2000 characters; no long step hides an additional comparison lemma.

For C4, citations.json contains a literal substring (in fact the complete statement) for every cited node at each step. I checked their hypotheses in the step descriptions above. For C1, each substantive input is one of these explicit nodes; complement density, localization at one prime in a finite spectrum, coefficient reduction, and inversion have their arguments in the steps rather than new nodes. For D1–D2, none of the children states existence of the item's rational étale parameter over the original finite-height base. They are analytic, completion, composition, coarsening, separating-field, chart or model inputs to that proof. The generic étale tools are existing Mathlib leaves, and their use is declared in split_report.tool_uses. No SGA source is used.

The delivery continuation on 2026-10-19 passed its initial dry run at bcf924e575. The subsequent push exited without pushing because the refreshed DAG contains two more source-filename collisions, def-trf-birational-valuation-neighbourhood-data and def-trf-horizontal-valuation-curve-data. I opened both complete records: the former defines valuation cylinders and affine birational neighbourhood systems; the latter defines valuation bases, relative curves and flat closure data. Neither asserts any of the six valuation/analytic lemmas flagged by the check. The twelve pairwise distinctions above record this reading. No statement or proof was changed. The final dry run is repeated after this report-only repair.

## Unfinished work

No part of the one-level split is intentionally left unfinished. The eight new nodes are unsplit inputs for later stage-1 work. The full server dry run passed after the duplicate-review additions. A final wording check made the finite-extension hypothesis in the decompletion child global and made the quantifier on separating parameters explicit; its citation quotes were refreshed. The final server dry run and direct delivery validate those wording repairs.
