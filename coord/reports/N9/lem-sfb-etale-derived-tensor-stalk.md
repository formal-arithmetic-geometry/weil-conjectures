# N9 stage-1 repair: lem-sfb-etale-derived-tensor-stalk

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-derived-tensor-stalk.json`: existing item, unchanged statement, repaired split; parent proof is 2144 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-stalk-constant-complex-exactness.json`: statement-only, status unsplit, no Mathlib match. Exact module stalk and constant functors on unbounded complexes, with natural constant-germ chain retraction.
- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-stalk-total-tensor-comparison.json`: statement-only, status unsplit, no Mathlib match. Canonical direct-sum total tensor stalk comparison, signed differential and two-variable chain-map naturality.
- `citations.json`: verbatim statement quotations for every parent step/node pair.

## Attachments

None. I searched `lean/WeilConjectures/` by the blueprint tag and derived tensor/stalk concepts and read `lean/Sheaf/AlgebraicGeometry/EtaleDerivedTensorStalk.lean`. The main declaration `AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso` ends in `sorry`; the three proved structural instances do not prove the item. The upstream ringed-space stalk criterion concerns Zariski ringed spaces, not this etale coefficient category. No finished project declaration proves either complete new statement.

## WANTED

None. All sources used were available locally.

## Repair and retained work

The return asks for new independently assignable arguments, an unchanged parent statement, and a parent proof of at most 3000 characters. The named sandbox initially contained only dispatcher dotfiles: no DAG nodes, report or search log. I copied the current read repository item as the repair baseline and preserved its statement and all maintainer-owned metadata. I have not edited the library or used git, Lean, Lake or compilation tools. The source module remains `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk`.

The two new nodes have their own schemes, coefficient rings, geometric points and complexes. They are delivered with empty proof and proof_deps, so other workers can take their arguments independently. Their source labels and blueprint ancestor `det-ctf-finite-proper-tor` are explicit, with the parent in the via chain. I searched the whole DAG and imported blueprint for constant complexes, stalks, total tensors and the source tags before creating them; the nearest existing statements are distinguished below. All Mathlib searches were actually run through the required msearch command and their returned names were read. Each new node records its own first and second semantic phrasings, Loogle and source grep results from searches.jsonl, without inventing queries. Ordinary monoidality in Mathlib Sites/Point/Monoidal.lean:35-140 and the general bifunctor/total tensor constructions are ingredients, not the complete new statements. I also read the project's ConstantSheaf.lean:45-122, the signed tensor helpers and mapHomologicalComplexδNatTrans in WeilConjectures/Mathlib/Algebra/Homology/Monoidal.lean, and the homotopy comparison in WeilConjectures/Algebra/Homology/HomotopyCategory/OplaxMonoidal.lean. These give reusable APIs to future workers; none alone states both complete new claims under exactly their etale hypotheses.

The first new node takes the whole of original Step 1: lifting exactness from abelian groups to A-modules, commuting with cohomology, the constant-presheaf stalk calculation with its natural A-linear germ map, and exact sheafification of constant acyclic complexes. This is a comparison between the module-valued functors and their unbounded complex functors, including a specified natural chain isomorphism. It is not merely an isolated exactness fact or an elementary assertion that an acyclic complex remains acyclic once exactness is already given.

The second new node takes the whole of original Step 2: the countable degreewise coproducts, A-linear colimit comparisons, ordinary tensor comparison on every summand, verification of both differential terms including (-1)^p, and two-variable chain-map naturality. Existence of an unnormalized total-complex isomorphism alone cannot supply its stipulated coprojection/germ formulas and naturality. No derived tensor or K-flat assertion is claimed in this new node, so it does not restate the parent or one of its clauses.

Original Step 3 remains an elementary assembly using precisely these two nodes: for every acyclic E, take its actual constant complex cE, apply the K-flat condition to cE tensor P, and identify its acyclic stalk with E tensor SP. This avoids adding a duplicate of the existing general ringed-site K-flat stalk criterion. Original Step 4 remains the K-flat-resolution assembly. Original Step 5's full independence and naturality argument is supplied by the existing resolving-subcategory equivalence and unique-extension statement `lem-weil-pbc-site-derived-tensor-descent`, with the two factor-wise quasi-isomorphism checks still explicitly written in the parent. Its proof is not silently compressed into an unsupported assertion. The original argument text is preserved verbatim later in this report as a handoff to the workers on the new nodes.

There is no STATEMENT-DISPUTED: the statement is unchanged and is correct for the ordinary constant coefficient sheaf. No condensed coefficients, completed tensor product, bounded derived category, or scheme-theoretic structure-sheaf stalk is substituted. No route involving an SGA source is used.

## Unfinished work

The two new statement-only nodes deliberately await their own stage-1 workers. No mathematical gap is left in the parent assembly beyond those explicitly cited nodes. Server check_dag and review_split both passed before this report; their inherited route advisories concern existing citers of the item, not new edges. The first deliver.py --no-push run passed with commit 4c034a4770a. After that check I explicitly introduced C and E in the first new statement and added the module-sheaf definition citation to both new statements; these clarify the existing search questions without changing the mathematics. A final dry run checks this final wording before the push.

## Review by N9

I read the current blueprint chapter, unit sk-prop-ctf-finite-proper and its Tor proof `sk-prop-ctf-finite-proper-tor.proof.md`, especially "From constant modules to all sheaves". The unbounded stalk identity used there is exactly the parent's statement. I read Stacks sites-cohomology.tex, labels lemma-check-K-flat-stalks (0DEN), lemma-K-flat-resolution (06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), definition-derived-tor (06YU), and the proof of lemma-pullback-tensor-product (07A4). For the first new node I read sites-modules.tex lemma-sheafification-exact (03EI), lemma-stalk-exact-modules (04EQ), and etale-cohomology.tex lemma-stalk-exact (03PT). For the second I read the totalization paragraph of 07A4 and sites-modules.tex lemma-tensor-product-pullback (03EL). The constant coefficient specialization permits the simple acyclic constant-complex test instead of Stacks' more elaborate arbitrary ringed-site proof. The source metadata and the report identify the agent-written specialization.

Parent Step 1 uses the first new node for exactness, acyclicity, quasi-isomorphisms and the natural constant-germ retraction, and the second for the specified chain comparison. I checked that these conclusions are explicitly in the statements, rather than only in a prospective proof. The hypotheses require only a scheme, commutative ring and geometric point; all are already introduced by the parent. In particular the module comparison is A-linear and its ring is A, not the structure-sheaf local ring. Both new nodes cite the notions that introduce their objects.

Parent Step 2 uses those same two statements and the two definitions of K-flatness. I opened both definitions: the sheaf definition tests F tensor P for every acyclic sheaf complex F, so I use cE tensor P in this order, not an unmentioned symmetry theorem. The new constant-complex lemma gives the acyclicity of cE; exact stalks and the new tensor comparison give exactly E tensor SP. The ordinary-module definition then gives K-flatness of SP. No extra hypothesis such as bounded-above, flat terms or finite coefficients enters this argument. This is a genuine few-line application of the two extracted lemmas, so it stays an elementary assembly step.

Parent Step 3 uses `lem-kun-flat-resolution-existence`, whose statement explicitly supplies unbounded K-flat resolutions with flat terms. Those flat terms matter in the next step. The new exactness lemma supplies quasi-isomorphisms after taking stalks, and Step 2 supplies K-flatness. The definitions of derived tensor and module K-flat resolution compute the two objects by the displayed total tensor complexes; localization of the new comparison is therefore the desired isomorphism. I opened each cited definition and checked both its coefficient category and its quantifiers. No termwise flatness is demanded of arbitrary input complexes.

Parent Step 4 uses `lem-kun-derived-tensor-well-defined`, whose statement handles a quasi-isomorphism between K-flat models tensored with any complex, and the module definition, which explicitly includes preservation of quasi-isomorphisms by a fixed K-flat factor. The stalks of the two fixed factors are K-flat by Step 2, so both module comparisons apply. The two-variable naturality equation in the second new node commutes with these maps; its equation also commutes with their inverses and composites. I opened `lem-weil-pbc-site-derived-tensor-descent`: it supplies the resolving-subcategory equivalence for K-flat objects WITH flat terms, natural total-tensor comparison, compatibility with quasi-isomorphism inversion, and existence/uniqueness of extension of a natural transformation of the restricted bifunctors. We choose flat-term resolutions in Step 3 and a small skeleton of the etale site, hence meet exactly its hypotheses. Apply it separately to the comparison and its inverse to obtain an isomorphism, not just a natural transformation. Its statement provides this formal extension; I do not cite a mere definition of localization for a missing extension theorem. The three off-unit homological tools are declared in split_report.tool_uses.

I tested the new statements on zero complexes, A the zero ring, and on complexes concentrated in degrees p and q, including odd p and negative p. For concentrated complexes the displayed coprojection equation reduces to the ordinary balanced tensor/germ map; the differential has the same (-1)^p on both sides. For arbitrary unbounded inputs the index set p+q=n is small and countable, so there is no product-totalization or convergence assumption. On constants the degreewise germ comparison commutes with arbitrary differentials by its A-linear naturality. An empty scheme has no geometric point, so the assertions correctly become vacuous rather than constructing one. Neither the acyclic test nor the stalk comparison needs enough points; one specified point suffices. The parent remains natural in BOTH derived variables, with the canonical comparison fixed by the normalized total-complex map.

I checked B--E against the actual JSON: the new nodes are statement-only and self-contained, with matching notion dependencies and valid TeX; sources use the read Stacks tags and labels; recorded searches match the actual log. I ruled out an attachment of the complete parent because of its explicit sorry. I used existing resolution, independence and localization nodes instead of creating further duplicates, and wrote the close duplicate distinctions below. Every use in the parent has a verbatim statement quote in citations.json. The parent has no step over 2000 characters and the whole proof is 2144 characters. The original proof and its new destinations are retained below, so the repair adds separately assignable work rather than merely shortening prose.

## Not duplicates

lem-sfb-etale-stalk-constant-complex-exactness vs def-kun-constant-sheaf: the existing node defines constants and termwise constant complexes; it does not assert exactness of the module stalk functor or the natural A-linear constant-germ chain retraction with cohomology comparisons.

lem-sfb-etale-stalk-constant-complex-exactness vs def-weil-pbc-torsion-etale-sheaf: the existing statement concerns "Torsion abelian sheaf on the small etale site"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs det-pe-injective-acyclicity-reduction: the existing statement concerns "Reduction of the acyclicity to affine étale objects"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-a1-integral-constructible-reduction-fibres: the existing statement concerns "Ordinary finite quotients and adic fibres of an integral constructible heart object"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-asd-supported-kummer-scalar-derived-units: the existing statement concerns "Derived universal properties of supported scalar maps"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-asd-supported-kummer-scalar-source: the existing statement concerns "Derived scalar extension of a closed supported constant sheaf"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-constructible-constant-exact: the existing statement concerns "Exactness of finite constant etale sheaf sequences"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-exc-proetale-proper-open-sheaf-comparison: the existing statement concerns "Proper/open comparison for pro-etale module sheaves"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-finrepair-constant-finite-comparison: the existing statement concerns "Constant coefficients under a finite normalization comparison"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-galois-flc-set-stalk-finite: the existing statement concerns "Geometric stalks of finite locally constant sheaves of sets are finite"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-kun-cd-stalk-criterion: the existing statement concerns "Vanishing of a higher direct image, checked at a geometric point"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-kun-geometric-point-derived-constants: the existing statement is an equivalence for integer coefficients on Spec of an algebraically closed field; the new statement treats every scheme and every commutative coefficient ring and does not assert the stalk functor is an equivalence.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-kun-integral-derived-tensor-bounded-torsion: the existing statement concerns "Integral derived tensor: lower bound and torsion cohomology"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-kun-pullback-constant: the existing statement concerns "Inverse image of a constant sheaf"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-kun-stalk-faithful-derived: the existing statement concerns "Stalk faithfulness for derived objects"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-bounded-above-rhom-hyperext: the existing statement concerns "Finite-diagonal hyper-Ext spectral sequence in the bounded-below second argument"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-constructible-ext-filtered-colimit: the existing statement concerns "Sheaf Ext from a bounded-above constructible etale complex commutes with filtered colimits"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-etale-godement-supported-exact-model: the existing statement concerns "Etale Godement model exact on supported coefficient terms"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-etale-point-product-acyclic: the existing statement concerns "Geometric-point product sheaves: adjunction, exactness and evaluation acyclicity"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-etale-support-aisle-generators: the existing statement concerns "Supported etale generators for cohomological support filtrations"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-integral-chart-logification-thickening: the existing statement concerns "Integral chart logification on arbitrary schemes and strict first-order restriction"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-per-log-smooth-differential-local-freeness: the existing statement concerns "Finite freeness of logarithmic differentials at a log-smooth geometric point"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pod-lisse-tensor-and-scalar-extension: the existing statement concerns "Tensor products, scalar extension and stalks of lisse sheaves of modules"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pod-point-dualizing-complex: the existing statement concerns "Dualizing complex of the point"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pur-constant-two-term-resolution: the existing statement concerns "Two-term constant-sheaf resolution of Z/ell^N and its tensor augmentation"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pur-finite-field-derived-tensor-summand: the existing statement concerns "The diagonal summand of derived tensor for an extension of finite fields"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pur-finite-kummer-level: the existing statement concerns "Finite Kummer level of the Tate twist"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pur-ringed-site-injective-mono-restriction: the existing statement concerns "Injective modules on a ringed site restrict surjectively along monomorphisms"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pur-support-exact: the existing statement concerns "The exact sequence of supported sections for injective objects"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-pur-support-quotient-product: the existing statement concerns "Normalized multiplication of support quotient sheaves on products"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-etale-smooth-stratified-ctf: the existing statement concerns "Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-etale-stalk-tor-test: the existing statement concerns "Geometric-stalk test and inverse-image stability of Tor intervals"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-etale-stratified-stalk-identification: the existing statement concerns "Derived geometric stalk of a constant local model"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-filtered-coefficient-tensor-bounds: the existing statement concerns "Finite coefficient filtration preserves constructibility and the cohomological interval"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-intrinsic-realization-origin-comparison: the existing statement concerns "IntrinsicRealizationOriginComparison"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-open-tor-bound-stalk-filtered-extension: the existing statement concerns "Finite constant-module tests detect etale Tor amplitude"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-proetale-residue-module-tensor-homology: the existing statement concerns "Ordinary tensor homology for modules over a constant field quotient"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sf-proetale-residue-tor-test: the existing statement concerns "The residue test on the pro-étale site"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-constant-to-continuous-scalar-flat: the existing statement concerns "Continuous coefficients are flat over discrete constant PID scalars"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-etale-derived-tensor-stalk: the parent asserts a natural isomorphism of DERIVED tensor bifunctors; this new node is a prerequisite about exact termwise constant/stalk functors and contains no derived tensor assertion.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-finite-constant-model-two-term-free-resolution: the existing statement concerns "Finite scalar local models have two-term finite-free sheaf resolutions"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-flat-scalar-cyclic-resolution: the existing statement concerns "Two-term scalar quotient resolutions after flat sheaf extension"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-geometric-stalk-tensor-constant-single: the existing statement concerns "Geometric stalks commute with derived tensor against a constant module"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-module-upper-star-kflat-quasi-iso: the existing statement concerns "The pullback of module objects preserves K-flat quasi-isomorphisms"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-scalar-model-finite-flat-resolution: the existing statement concerns "Finite flat scalar-model resolutions on a ringed site"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-scalar-normalized-constant-models: the existing statement concerns "Natural constant models from scalar-normalized module equivalences"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-sfb-scalar-presentation-cokernel: the existing statement concerns "A specified scalar presentation gives the same coefficient-sheaf cokernel"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-associated-log-universal-stalks: the existing statement concerns "Associated log structures: construction, universal property and geometric stalks"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-oriented-closed-base-localization: the existing statement concerns "Closed complementary subtopoi: factorization and supported module sheaves"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-oriented-source-localization: the existing statement concerns "Open and closed source recollement on a vanishing topos"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-proper-surjection-etale-section-equalizer: the existing statement concerns "Proper surjections give descent of small etale pullback sections"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-sheafified-module-differentials-cokernel: the existing statement concerns "Sheafified presentation of modules of differentials"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-simple-constructible: the existing statement concerns "Simple constructible sheaves"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-trf-topos-complement-module-stalks: the existing statement concerns "Module support, adjunctions and stalks for complementary subtopoi"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-constant-sheaf-geometric-stalk: the existing statement fixes an abelian group and proves a single stalk map is invertible; the new statement concerns module-valued exact functors, unbounded complexes, a natural A-linear chain retraction and cohomology for both functors.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-constructible-abelian-zn-module-constructible: the existing statement concerns "A constructible abelian sheaf killed by n is a constructible sheaf of Z/n-modules"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-etale-inverse-image-small-universe: the existing statement concerns "Ordinary étale inverse image preserves the scheme coefficient universe"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-etale-open-cover-shriek-ses: the existing statement concerns "Open-cover short exact sequence of etale extensions by zero"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-etale-section-germ-iso: the existing statement concerns "Constant sheaf trivialization from section germs"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-inverse-image-stalk-germ: the existing statement concerns "Stalk of an inverse image, compatible with germs of pulled-back sections"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-localization-free-resolution: the existing statement concerns "Free resolution of localization on a slice"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-localization-inverse-image-coherence: the existing statement concerns "Coherent localization comparison for exact inverse image"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-module-presheaf-sheafification-exact: the existing statement concerns "Presheaves of O_X-modules form an abelian category with sectionwise kernels and cokernels, and sheafification is exact"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-sets-etale-inverse-image-stalk-germ: the existing statement concerns "Stalk of the etale inverse image of a sheaf of sets, with germs"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-sets-etale-stalk-finite-limits: the existing statement concerns "Etale stalks of sheaves of sets commute with finite limits"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-sets-sheafification-geometric-stalk: the existing statement concerns "Geometric stalks of a presheaf of sets and of its sheafification agree"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-sheaf-tensor-closed: the existing statement concerns "A-valued sheaves on an essentially small site: Grothendieck abelian, symmetric monoidal closed under the sheafified tensor product"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-sheafification-geometric-stalk: the existing statement identifies the stalk of an abelian presheaf with its sheafification; the new statement asserts exact module functors on unbounded complexes and their normalized constant-complex retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-site-r-module-presheaf-sheafification-exact: the existing statement concerns presheaf evaluation and sheafification on a general site; the new statement constructs the etale constant/stalk chain retraction and both cohomology comparisons over the ordinary ring A.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-pbc-torsion-sheaf-characterizations: the existing statement concerns "Characterizations of torsion abelian sheaves on the etale site"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs lem-weil-point-fibre-equivalence: the existing statement concerns "The fibre functor at the geometric point is an equivalence"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs new-r2-etale-abelian-kan-comparison-locally-surjective: the existing statement concerns "Local surjectivity of the concrete underlying-set Kan comparison"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-constant-complex-exactness vs sk-def-smooth: the existing statement concerns "Smooth and allowed coefficients"; it does not give the pair of exact module-valued constant/stalk complex functors on every scheme together with their normalized natural chain retraction.

lem-sfb-etale-stalk-total-tensor-comparison vs cor-galois-lisse-representations: the existing statement concerns "Lisse sheaves and continuous representations"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs cor-pur-smooth-admissibility: the existing statement concerns "Smooth morphisms satisfy the preservation clauses"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs cor-weil-boundary-duality-discharge: the existing statement concerns "The finite-stage boundary input is a consequence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-coef-ringed-tensor-hom-model: the existing statement concerns "Canonical closed tensor-Hom representative model on a ringed site"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-coef-semilinear-derived-calculus: the existing statement concerns "Ordinary derived semilinear calculus interfaces"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-coef-semilinear-geometry-base: the existing statement concerns "Geometry base fields for coefficient linear operations"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-coef-semilinear-geometry-derived: the existing statement concerns "Derived geometric system operations and normalization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-coef-semilinear-geometry-ops: the existing statement concerns "Canonical geometric mate and projection words"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-coef-semilinear-system-models: the existing statement concerns "Generic strict semilinear system constructions and representative normalization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-kun-constant-projection-morphism: the existing statement concerns "Canonical constant-coefficient derived projection morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-kun-projection-formula-map: the existing statement concerns "The projection-formula morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pd-proetale-section-module-functors: the existing statement concerns "Normalized tensor structures on existing pro-etale section-module functors"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pd-section-derived-realization: the existing statement concerns "Canonical derived section-module realization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pd-section-derived-tensor-data: the existing statement concerns "Canonical derived section-module tensor data"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-cochain-coefficient-arrows: the existing statement concerns "Canonical scalar-association and transition arrows on cochain sheaves"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-cochain-coefficient-universe-transport: the existing statement concerns "Canonical common-universe transport of ring and module sheaves"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-cochain-tensor-coherence-data: the existing statement concerns "Canonical cochain ringed-pullback and coherence data"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-completed-pullback-tensor-comparison: the existing statement concerns "Canonical completed, rational and common-stage tensor pullback comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-etale-scalar-pullback-iso: the existing statement concerns "Canonical derived scalar and pullback isomorphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-exceptional-coefficient-tensor-maps: the existing statement concerns "Canonical tensor and unit transport maps for exceptional coefficient comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-finite-pullback-tensor-comparison: the existing statement concerns "Canonical finite derived pullback tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-open-coefficient-normalizations: the existing statement concerns "Exact-pullback and open-unit coefficient normalizations"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-ringed-coefficient-projection-data: the existing statement concerns "Normalized coefficient projection interfaces"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-scalar-pullback-representative-data: the existing statement concerns "Canonical scalar/pullback representative data"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-smooth-pullback-exchange: the existing statement concerns "Smooth pullback exchange for exceptional inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-pur-system-tensor-mate-arrows: the existing statement concerns "Canonical tensor and proper/open arrows for varying coefficient systems"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-evaluation-hom-site-comparison: the existing statement concerns "Evaluation-induced derived Hom comparison for the etale-proetale morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-finite-coefficient-site-chain-tensor: the existing statement concerns "Canonical finite coefficient site comparison on total tensor complexes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-finite-coefficient-site-hom-arrow: the existing statement concerns "Canonical finite coefficient site internal-Hom arrow"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-finite-coefficient-site-scalar-arrow: the existing statement concerns "Canonical finite coefficient site scalar comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-open-normalization-data: the existing statement concerns "Geometric and operation data for open tensor normalization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-point-fibre-tensor-common-stage: the existing statement concerns "Canonical common-stage point tensor and coefficient unit"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-point-fibre-tensor-finite-models: the existing statement concerns "Canonical finite point tensor normalization on K-flat representatives"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-point-fibre-tensor-models: the existing statement concerns "Canonical integral representative normalization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-point-fibre-tensor-rational-compatibility: the existing statement concerns "Canonical rational point tensor, unit, and scalar compatibility"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-point-fibre-tensor-reduction: the existing statement concerns "Canonical module scalar tensor data and finite reduction squares"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sf-point-fibre-tensor-system: the existing statement concerns "Strong symmetric tensor comparison data for the point fibres"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-condensed-pullback-tensor-comparison: the existing statement concerns "Normalized condensed-module pullback tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-module-object-projection-map: the existing statement concerns "Canonical derived projection map for condensed module objects"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-proetale-trace-coefficient-interfaces: the existing statement concerns "Canonical internal-module trace coefficient interfaces"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-ringed-derived-comparison-data: the existing statement concerns "Data of normalized derived monoidal comparisons of ringed topoi"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-ringed-projection-coherence-data: the existing statement concerns "Recorded data for tensor projection coherence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-ringed-slice-comparison-model: the existing statement concerns "Normalized ringed slice comparison data"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sfb-scalar-hom-comparison-data: the existing statement concerns "Actual scalar-adjunction and normalized tensor-Hom comparison data"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sp-constant-scalar-pullback-comparison: the existing statement concerns "Canonical constant-coefficient scalar extension, direct image and pullback comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-sp-semilinear-constant-ring-operations: the existing statement concerns "Constant-ring semilinear system operations and normalized evaluation mates"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-canonical-ringed-tensor-comparison: the existing statement concerns "Normalized ordinary tensor comparison data"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-four-corners: the existing statement concerns "Four finite-level corners"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-level-map-corners: the existing statement concerns "Four finite-level rectangle corners"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-normalized-origin-scalar-comparisons: the existing statement concerns "Canonical quotient scalar-extension unit and associator"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-projection-formula-map: the existing statement concerns "Projection-formula map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-ringed-tensor-square-presentation: the existing statement concerns "Representative presentation of a commutative ringed tensor square"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs def-weil-pbc-witness-compatibility: the existing statement concerns "Witness compatibility condition"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-cor-sf-direct-image-ctf-open-tor: the existing statement concerns "Scalar projection formula and the Tor bound for an open immersion"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-formal-closed-support-ii-limits: the existing statement concerns "Closed support commutes with derived limits of sequences"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-pe-finite-tor-comparison-noetherian: the existing statement concerns "Tor amplitude under comparison for Noetherian coefficients"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-prop-sfb-cartesian-coefficients-twists: the existing statement concerns "Inverse image of Tate twists"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-sp-integral-direct-image-tower: the existing statement concerns "Tower description of the integral compactly supported direct image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-sp-purity-bc-factors: the existing statement concerns "Base change of the orientation and of the tensor map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-sp-reduction-compatibilities: the existing statement concerns "Coefficient comparisons: units, composition and purity"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-sp-scalar-extension-functor: the existing statement concerns "The derived extension-of-coefficients functor and its associativity"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-thm-sf-pf-field-localizing: the existing statement concerns "The proper projection formula on the rational localizing categories"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs det-thm-sfb-proper-base-change-rational: the existing statement concerns "Proper direct image, base change and projection formula for $E$ and $\overline{\mathbf Q}_\ell$"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-amb-cartier-kummer-map: the existing statement concerns "A Cartier divisor gives a supported Kummer map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-amb-finite-tate-site-descent: the existing statement concerns "Finite Tate coefficients descend from pro-etale to etale sites"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-amb-tensor-projection-adjunct: the existing statement concerns "Adjoint of a tensor-projected morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-asd-etale-finite-twist-pullback: the existing statement concerns "Finite Tate lines on the small etale site and their pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-asd-etale-finite-twist-pullback-rest: the existing statement concerns "Finite Tate pullback derived and exponent coherence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-asd-supported-kummer-scalar-derived-units: the existing statement concerns "Derived universal properties of supported scalar maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-cbc-derived-finite-quotient-coherence: the existing statement concerns "All-quotient coherence of the canonical finite evaluation of tower pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-derived-system-evaluation-calculus: the existing statement concerns "Coherent derived reduction, limit adjunction and fiberwise evaluation"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-etale-hom-thick-locus: the existing statement concerns "Triangulated compatibility of the evaluation-defined scalar Hom comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-etale-tensor-model-comparison: the existing statement concerns "Unique flat-model normalization of the étale scalar tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-finite-etale-descent: the existing statement concerns "Étale recovery of the closed exceptional quotient comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-integral-finite-extension: the existing statement concerns "Integral duality and a finite extension of coefficient fields"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-ringed-pullback-hom-evaluation-comparison: the existing statement concerns "Evaluation-defined Hom comparison for ringed pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-semilinear-operations-existence: the existing statement concerns "Geometric and coefficient operations on a fixed semilinear system calculus"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-semilinear-system-existence: the existing statement concerns "Ordinary semilinear system calculus and cartesian internal Hom"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-coef-signed-single-dual-restriction: the existing statement concerns "Normalized slice comparison for a single coefficient dual"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-derived-right-exact-tensor-comparison: the existing statement concerns "Normalized tensor comparison for a right exact strong monoidal functor"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-exc-proetale-constant-support-projection: the existing statement concerns "Constant-coefficient projection for compact support"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-exc-support-scalar-projection-normalization: the existing statement concerns "Normalization of support scalar mate as a projection arrow"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fd-artin-schreier-finite-lisse: the existing statement concerns "Artin–Schreier character sheaves over arbitrary finite rings are flat lisse lines"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fd-base-change: the existing statement concerns "Base change of the transform"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fd-flat-constructible-tensor: the existing statement concerns "Tensor with a flat constructible étale sheaf preserves bounded constructibility"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-constructible-flat-cohomology-tor-bound: the existing statement concerns "Flat bounded cohomology gives finite Tor amplitude"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-open-scalar-exchange: the existing statement concerns "Scalar extension respects the open base-change comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-open-scalar-tensor-normalization: the existing statement concerns "Open scalar comparison with unit, tensor and composition normalization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-operation-reduction: the existing statement concerns "Basic operations and coefficient reduction"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-proetale-scalar-mate-normalization: the existing statement concerns "Pro-etale scalar mate restricts to the specified projection arrow"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-reduction-open-etale-origin: the existing statement concerns "Bounded etale witnesses for finite reduction and open extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-fix-tensor-pullback-square: the existing statement concerns "Tensor inverse-image comparisons commute around an open square"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-geo-cartier-coeff-extension: the existing statement concerns "Derived scalar extension of a closed supported constant sheaf"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-0f0f: the existing statement concerns "Projection formula, integer coefficients"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-bc-kunneth-compat: the existing statement concerns "Cohomology of the base change map through the Kunneth identification"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-derived-pullback-composition-monoidal: the existing statement concerns "Canonical derived etale inverse-image composition is monoidal"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-geometric-point-projection-comparison: the existing statement concerns "Geometric-point projection morphism agrees with the constant-section projection morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-geometric-point-pullback-tensor-normalization: the existing statement concerns "Tensor normalization of the pullback/stalk evaluation comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-integral-derived-tensor-bounded-torsion: the existing statement concerns "Integral derived tensor: lower bound and torsion cohomology"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-inverse-image-monoidal: the existing statement is for derived inverse image along a scheme morphism; the new statement is a chain-level geometric stalk comparison with specified coprojection/germ formulas and no derived localization.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-kunneth-map-agrees: the existing statement concerns "Compatibility of the Kunneth map with Leray, proper base change and the projection formula"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-kunneth-map-natural: the existing statement concerns "Naturality of the Kunneth map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-kunneth-via-0f1n: the existing statement concerns "Compatibility of the Kunneth map with the projection-formula variant"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-kun-proj-formula-natural: the existing statement concerns "Naturality of the projection formula"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pd-module-ringed-topos-derived-comparison: the existing statement concerns "Module-object and ringed-topos derived tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pd-ringed-tensor-adjunction-mate: the existing statement concerns "Identify ringed tensor comparisons with specified adjunction mates"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pd-section-derived-tensor-normalization: the existing statement concerns "Derived tensor and actual pullback tensor arrows under section equivalence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pd-section-ordinary-oplax-normalization: the existing statement concerns "Ordinary module pullback oplax mate on balanced generators"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pe-constructible-comparison-tensor-test-reflection: the existing statement concerns "Reflection of a single comparison tensor test"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-per-galois-cover-module-descent: the existing statement concerns "Module descent along a connected finite Galois cover"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-per-galois-descent-monodromy-tensor: the existing statement concerns "Monodromy and tensor of modules descended along a finite Galois cover"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-per-galois-partition-tensor-closure: the existing statement concerns "Tensor closure for a fixed Galois partition"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-per-local-system-tensor-monodromy: the existing statement concerns "Tensor comparison for arbitrary torsion local systems"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-per-noetherian-supported-product-calculus: the existing statement concerns "Supported products and Cartier interchange on ordinary etale sites"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-per-tate-twist-lisse-line: the existing statement concerns "The Tate twist line is a rank-one lisse adic sheaf and twisting is the lisse tensor"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pod-etale-stalk-tensor-scalar: the existing statement is for sheaves of modules and scalar extension; the new statement is for unbounded signed total complexes, includes the direct-sum coprojections and differential, and asserts two-variable chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pod-finite-projective-tensor-hom: the existing statement concerns "Internal Hom with a finite projective module"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pod-frobenius-cup-transport: the existing statement concerns "Finite-coefficient Frobenius transport commutes with mixed-support cup product"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pod-integral-pullback-composition: the existing statement concerns "Composition isomorphism for integral derived pullbacks"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pod-lisse-tensor-and-scalar-extension: the existing statement concerns "Tensor products, scalar extension and stalks of lisse sheaves of modules"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pod-point-duality-coefficient-compatibility: the existing statement concerns "Point dualizing identification is compatible with coefficient change"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-adic-projection-shift-coherence: the existing statement concerns "Shift compatibility of the compact-support projection and trace transpose"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-closed-supported-cup-vanishing: the existing statement concerns "Restriction to a closed support detects the zero action on supported cohomology"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-cochain-comparison-monoidal-equations: the existing statement imposes equations on an already specified cochain pullback comparison; the new node establishes and normalizes the geometric-stalk total tensor comparison itself.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-cochain-pullback-tensor-coherence: the existing statement concerns pullback between ringed sites with coefficient ring isomorphisms and composition coherence; it does not identify the ordinary module-valued geometric stalk and its canonical coprojection/germ map over A.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-coefficient-associator-shifts: the existing statement concerns "Shift compatibility of balanced derived scalar associators"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-coefficient-pullback-coherence: the existing statement concerns "Balanced coherence of canonical coefficient pullback comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-coefficient-pullback-comparison: the existing statement concerns "Canonical inverse-image coefficient comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-coefficient-pullback-shifts: the existing statement concerns "Shift compatibility of normalized inverse-image coefficient comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-coefficient-scalar-shifts: the existing statement concerns "Counit-normalized coherent shifts on scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-coefficient-scalar-units: the existing statement concerns "Multiplication units for derived scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-compact-support-completed-projection-coherence: the existing statement concerns "Completion coherence for the integral projection mate"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-completed-operation-tower-substitution: the existing statement concerns "Coherent substitution of normalized systems into completed operations"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-condensed-tate-realization: the existing statement concerns "Realization of the reconstructed Tate tower in the condensed coefficient category"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-derived-pullback-tensor-iso: the existing statement concerns "Derived pullback commutes with derived tensor product on the constructible categories"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-etale-closed-constant-tensor: the existing statement concerns "Closed constant coefficient tensors and pullback on the etale site"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-etale-compact-scalar-coherence: the existing statement concerns "Ordinary etale compact-support scalar compatibility with projection and composition"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-etale-exceptional-constant-tensor: the existing statement concerns "Constant-coefficient tensor calculus for the finite etale exceptional adjoint"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-etale-scalar-mate-projection: the existing statement concerns "Restriction of the derived coefficient mate equals the projection morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-etale-scalar-pullback-existence: the existing statement concerns "Existence of normalized derived scalar/pullback comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-etale-scalar-pullback-uniqueness: the existing statement concerns "Uniqueness of normalized derived scalar/pullback comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-exceptional-coefficient-comparison: the existing statement concerns "Counit-transpose coefficient comparison and tensor coherence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-finite-free-scalar-projection: the existing statement concerns "Finite-free scalar extension preserves the specified proper, open and compact projection maps on both sites"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-finite-kummer-level: the existing statement concerns "Finite Kummer level of the Tate twist"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-finite-projection-action-laws: the existing statement concerns "Tensor-action and open-counit identities for finite-level projection maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-finite-reduction-constructibility: the existing statement concerns "Finite quotient reduction preserves the finite constructible categories"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-finite-ring-site-tensor-transpose: the existing statement concerns "Etale/pro-etale transport of compact-support projection maps and their transposes over an arbitrary finite ring"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-independent-inverse-image-tensor-comparison: the existing statement concerns "Normalized tensor comparison for an algebraic inverse image at independent site sizes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-independent-normalized-scalar-composition: the existing statement concerns "Normalized composition of module scalar extensions"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-independent-ringed-tensorator-existence: the existing statement concerns "Existence of the tensorator for fixed scalar insertion at independent site sizes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-ambient-operation-models: the existing statement concerns "Ambient completion presentations for integral pullback and tensor"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-coherence-tower: the existing statement concerns "Coherence identities on normalized integral comparison towers"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-line-reduction-restriction: the existing statement concerns "Signed line reductions and restriction to the derived-complete integral category"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-operations-scalar-extension: the existing statement concerns "Integral derived operations commute with finite scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-tensor-reduction-tower-comparison: the existing statement concerns "Strict tensor comparison for finite coefficient-reduction towers"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-tensor-transition-compatibility: the existing statement concerns "Quotient compatibility of the normalized total tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-integral-tower-limit-comparison: the existing statement concerns "Derived limit of the strict integral comparison tower"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-inverse-image-scalar-comparison: the existing statement concerns "Inverse image commutes with extension of scalars, with its unit formula"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-inverse-image-tensor-comparison: the existing statement concerns "The unit-normalized tensor comparison for an isomorphic base change"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing statement concerns "Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-kflat-total-tensor-model: the existing statement concerns "K-flat total tensor model for flat-term resolutions"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-module-tensor-coefficient-equations: the existing statement concerns "Ordinary module tensor equations for coefficient change"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-module-tensor-composition-equation: the existing statement concerns "Ordinary tensor square for composite module pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-module-tensor-extension-equation: the existing statement concerns "Ordinary scalar-extension tensor equation"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-module-tensor-generator-calculus: the existing statement concerns "Pure tensors and normalized insertion naturality for sheaf modules"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-module-tensor-monoidal-equations: the existing statement concerns "Associativity and symmetry of the canonical ordinary module tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-ordinary-kunneth-finite-ring: the existing statement concerns "Ordinary Kunneth at a finite coefficient ring"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-proetale-inverse-image-tensor-comparison: the existing statement concerns "Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-proetale-restricted-tensor-finite-local-constancy: the existing statement concerns "Finite local constancy of a restricted tensor with bounded-above inputs"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-projection-comparison-etale-origin: the existing statement concerns "Etale-origin comparison intertwines compact-support projection maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-projection-formula-coefficient-coherence: the existing statement concerns "Unit and coefficient associativity of compact-support projection maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-ringed-coefficient-projection-cocycle: the existing statement concerns "Coefficient projection cocycle for ordinary derived ringed diagrams"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-ringed-site-pullback-dual-free-chart: the existing statement concerns "Invertibility of a pulled evaluation comparison on a finite-free chart"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-ringed-site-pullback-pairing-transfer: the existing statement concerns "Extension of module pairings along a ringed site morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-scalar-extension-tower-coherence: the existing statement concerns "Coherent quotient towers for integral scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-scalar-hom-comparison-tower: the existing statement concerns "Evaluation-defined scalar Hom maps respect coefficient towers"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-scalar-tensor-pullback-normalization: the existing statement concerns "Scalar/tensor pullback normalization on a K-flat representative"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-scalar-tensor-unit: the existing statement concerns "Scalar action unitor for a normalized signed tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-shifted-tensor-morphism-calculus: the existing statement concerns "Signed calculus of shifted derived tensor morphisms on ringed sites"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-signed-line-derived-base-change: the existing statement concerns "Signed line comparisons and their unbounded derived tensor action"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-support-quotient-product: the existing statement concerns "Normalized multiplication of support quotient sheaves on products"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-support-site-comparison: the existing statement concerns "Etale-proetale comparison for supported sections and their exterior products"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-supported-bottom-gluing: the existing statement concerns "Gluing supported cohomology in its lowest local degree"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-supported-cup-functoriality: the existing statement concerns "Pullback and symmetry of supported Kummer cup products"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-system-level-projection-formula-coherence: the existing statement concerns "Strict-system projection formula composition coherence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-system-normalized-tensor-closure: the existing statement concerns "Normalized semilinear systems are closed under tensor and inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-system-tensor-reduction-formula: the existing statement concerns "Tensor formula for actual semilinear reduction adjoints"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-tate-inverse-limit-base-change: the existing statement concerns "Base change of an ell-adic inverse-limit tower and of its finite reduction tensor"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-torsion-line-system-base-change: the existing statement concerns "Normalized tensor extension of compatible torsion line systems"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-varying-ring-tensor-comparison: the existing statement concerns "Normalized tensor comparison for one varying-ring inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-pur-weil-tate-datum-transport: the existing statement concerns "Transport of the Tate source datum"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-affine-chart-factorization-gluing: the existing statement concerns "Finite affine chart factorization and interval gluing"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-cbc-completed-pullback-unit-tower: the existing statement concerns "Completed pullback completion unit is invertible in the strict reduction tower"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-cbc-constant-tower-direct-image-normalization: the existing statement concerns "Constant strict towers and normalized derived direct image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-closed-support-tor-bound: the existing statement concerns "Closed support triangle adds one to the Tor upper bound"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-comparison-open-tensor-coherence: the existing statement concerns "Etale/pro-etale comparison respects the canonical open tensor map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-constant-semilinear-generator-comparison: the existing statement concerns "Scalar restriction identifies the single proper and open reduction generators"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-etale-generic-hom-triangle: the existing statement concerns "Internal-Hom comparison respects the finite stratification triangles"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-etale-hom-complex-pullback: the existing statement concerns "Pullback comparison of ordinary sheaf Hom complexes and source shifts"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-etale-local-dual-interval: the existing statement concerns "Uniform local models and Tor interval for a twisted coefficient dual"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-etale-smooth-stratified-ctf: the existing statement concerns "Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-exceptional-product-direct-image-compatibility: the existing statement concerns "Exceptional external product is compatible with immersion direct images"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-finite-cover-ctf-locality: the existing statement concerns "Finite-cover locality of bounded constructibility and a fixed Tor interval"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-finite-exchange-projection-commshift: the existing statement concerns "Finite geometric exchange and projection commute with shifts"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-finite-field-local-tensor-model: the existing statement concerns "Localized inverse-image constant models under field scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-finite-field-sheaf-scalar-extension: the existing statement concerns "Finite-field scalar extension of constructible pro-etale complexes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-generator-reduction-coherence: the existing statement concerns "Basic generator coefficient squares in semilinear systems"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-hom-comparison-finite-free: the existing statement concerns "The internal-Hom comparison for a bounded free model"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-hom-finite-projective: the existing statement concerns "Internal Hom with a finite projective module"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-immersion-completed-pullback-comparison: the existing statement concerns "Ordinary immersion pullback agrees with quotient-tower completed pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-integral-compactification-system-realization: the existing statement concerns "Coherent integral realization of compactification expressions and their maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-integral-line-tensor-comparison-representative: the existing statement concerns "K-flat line tensor models and finite balancing"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-integral-open-product-diagram-normalization: the existing statement concerns "Strict-diagram normalization of integral open product comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-open-comparison-tensor-normalization: the existing statement concerns "Tensor compatibility of the etale/pro-etale open-extension comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-open-operation-models: the existing statement concerns "Open operation comparisons with fixed tensor models and right square"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-open-tensor-normalization: the existing statement concerns "Open-extension unit normalization for derived tensor and base change"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-open-tor-bound-stalk-filtered-extension: the existing statement concerns "Finite constant-module tests detect etale Tor amplitude"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-pf-open-factor-coherence: the existing statement concerns "Completed open restriction, constructibility and normalization of the open maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-point-fibre-derived-tensor: the existing statement concerns "The point fibre functor preserves derived tensor at all coefficient stages"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-proetale-tensor-composition-unit: the existing statement concerns "The explicit pro-etale tensor pullback comparison preserves composite adjunction units"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-rational-slice-completed-evaluation: the existing statement concerns "Restriction compatibility for completed rational evaluation"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-reduction-pull-finite-evaluation: the existing statement concerns "Finite evaluation respects the specified reduction/pullback comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-ringed-finite-free-hom-base-change: the existing statement concerns "Evaluation comparison for a finite free change of ring sheaves"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-ringed-finite-free-tensor-complex: the existing statement concerns "Actual scalar tensor comparison on complexes and K-flat preservation"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sf-ringed-finite-free-tensor-data: the existing statement concerns "Strong scalar tensor comparison for supplied normalized derived models"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-adic-perfect-model-complete-reduction: the existing statement concerns "Completeness and residue calculation of a completed perfect coefficient model"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-adic-stratum-completion-unit: the existing statement concerns "Restriction of the completion unit to strata and covering slices"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-admissible-tensor-constructibility: the existing statement concerns "Tensor constructibility for admissible coefficients"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-coefficient-push-filtered-legs: the existing statement concerns "Flat coefficient push comparison from a bounded filtered module presentation"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-coefficient-sections-localization: the existing statement concerns "Coefficient sections over pro-étale objects agree with global sections after pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-condensed-support-projection-formula: the existing statement concerns "Natural support tensor projection formulas on unbounded condensed modules"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-dc-hom-scalar-adjunction: the existing statement concerns "Derived internal Hom under restriction of coefficient scalars"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-dc-tensor-preserves: the existing statement concerns "$\otimes^{\mathrm L}$ preserves bounded constructible complexes ($\ell$-adic $\Lambda$)"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-divisible-extension-derived-reduction: the existing statement concerns "Derived reduction of an extension by a divisible sheaf"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-etale-derived-tensor-stalk: the parent asserts a DERIVED tensor/stalk isomorphism; this new node treats ordinary signed total complexes and their normalized chain maps, with no K-flatness or derived comparison conclusion.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-etale-proetale-scalar-pullback-cube: the existing statement concerns "Etale/pro-etale inverse-image square commutes with derived scalar comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-geometric-stalk-tensor-constant-single: the existing statement concerns "Geometric stalks commute with derived tensor against a constant module"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-hom-flat-evaluation-roof: the existing statement concerns "Flat scalar comparison is the evaluation-normalized resolution roof"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-hom-scalar-chain-identification: the existing statement concerns "Strict scalar Hom identification and normalized evaluation square"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-integral-quotient-direct-image-comparison: the existing statement concerns "Unbounded quotient-scalar refinement of integral direct image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-integral-quotient-exchange-comparison: the existing statement concerns "Reduction of the actual unbounded integral exchange"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-integral-quotient-projection-comparison: the existing statement concerns "Reduction of the actual unbounded integral projection morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-internal-hom-dual-tor-amplitude: the existing statement concerns "Finite Tor amplitude of locally constant perfect duals"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-kflat-scalar-comparison-normalization: the existing statement concerns "Representative and adjunction normalization of scalar pullback comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-lattice-pullback: the existing statement concerns "Lattice inclusions and rationalization survive scheme pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-local-model-tor-bound-descent: the existing statement concerns "Tor bounds descend from bounded flat local models"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-localized-direct-image-comparison: the existing statement concerns "Localization of coefficients commutes with bounded-below direct image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-localized-site-tensor-restriction: the existing statement concerns "Restriction to a localized site commutes with the sheaf tensor product"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-locally-free-derived-scalars: the existing statement concerns "Derived scalar extension of locally finite free module sheaves"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-module-object-ringed-site-derived-comparison: the existing statement concerns "Module-object and ringed-site derived internal Hom agree"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-point-upper-star-tensor: the existing statement concerns "$p^*$ preserves tensor products"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-proetale-intrinsic-tensor-comparison: the existing statement concerns "Right-tensor comparison for intrinsic constant-ring realization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-proetale-tor-local-global: the existing statement concerns "Local and global finite Tor dimension on a quasi-compact pro-étale site"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-projection-comparison-etale-proetale: the existing statement concerns "Etale-to-proetale comparison of the canonical direct-image projection morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-qlbar-direct-image-comparison: the existing statement concerns "Algebraic-closure coefficient change commutes with bounded-below direct image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-comparison-tensor-adjunction: the existing statement concerns "Tensor and adjunction compatibility of canonical ringed-topos path comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-derived-monoidal-comparisons: the existing statement concerns "Monoidal and adjunction normalization of derived ringed-topos comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-derived-tensor-diagrams: the existing statement concerns "Coherence equations for explicit canonical derived comparison maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-derived-tensor-lift: the existing statement concerns "Symmetric monoidal coherence of a canonical derived tensor lift"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-derived-two-iso-comparison: the existing statement concerns "Specified geometric 2-isomorphism comparison on derived modules"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-kunneth-factorizations: the existing statement concerns "Two factorizations of the ringed-topos external product comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-projection-first-shift: the existing statement concerns "The ringed projection mate commutes with shifts in its direct-image input"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-projection-pullback-comparisons: the existing statement concerns "Normalized identity, composition and section pullback comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-projection-tensor-compatibility: the existing statement concerns "Tensor constraints and compatibility of normalized comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-projection-tensor-structure: the existing statement concerns "Canonical tensor structure in arbitrary recorded presentations"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-site-duality-maps: the existing statement concerns "Canonical coefficient-duality maps on a small ringed site"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-site-point-acyclic: the existing statement concerns "A conservative point family detects acyclicity"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-ringed-site-point-tensor: the existing statement gives existence of an isomorphism for a normalized ringed-site point; it does not state the coprojection/germ normalization or two-variable naturality. The new statement makes exactly those chain-level data explicit for the etale point, needed to descend the canonical comparison.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-scalar-hom-tensor-coherence: the existing statement concerns "Tensor coherence of the normalized scalar extension maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-scalar-internal-hom-tower-coherence: the existing statement concerns "Coefficient-tower and identity coherence for normalized internal Hom"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-scalar-inverse-image-tower-diagram: the existing statement concerns "Ordinary inverse-image and balanced scalar-tower square"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-scalar-ordinary-tensor-comparison: the existing statement concerns "Normalized ordinary scalar tensor comparison in independent site universes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-scalar-tensor-comparison: the existing statement concerns "Derived scalar tensor comparison on all K-flat representatives"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-scalar-tensor-tower-comparison: the existing statement concerns "Simultaneous normalized scalar tensor comparisons with coefficient coherence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-site-inverse-image-bilinear-adjunction: the existing statement concerns "Bilinear adjunction for the inverse image of a morphism of sites"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-site-inverse-image-multimap-universal: the existing statement concerns "Universality of inverse-image units for natural maps with finitely many inputs"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-tor-interval-local-detection: the existing statement concerns "Tor bounds detected on pro-etale covers and open-closed decompositions"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-trace-base-change-first: the existing statement concerns "Trace and base-change rearrangement before the first triangle"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sfb-trace-base-change-second: the existing statement concerns "Trace and base-change rearrangement before the second triangle"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-completion-mate-comparison: the existing statement concerns "The strict quotient-tower exchange realizes the completed-adjunction mate"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-direct-image-change-ring-transpose: the existing statement concerns "Restriction identifies the proper coefficient comparison with the pro-etale projection map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-direct-image-etale-mate-isomorphism: the existing statement concerns "The etale projection mate has the normalized pro-etale counit transpose"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-finite-coefficient-input-models: the existing statement concerns "Finite coefficient and site extension on bounded flat input models"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-finite-compact-support-domains: the existing statement concerns "Compact support and coefficient extension retain the finite-Tor domain"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-finite-ring-compact-support-projection: the existing statement concerns "Compact-support projection formula on pro-etale sites with arbitrary finite l-primary coefficients"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-flat-coefficient-chain-transpose: the existing statement concerns "Scalar extension of flat chain maps and their canonical derived transposes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-invertible-tensor-scalar-extension: the existing statement concerns "Tensor powers and duals of an invertible module after scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-proetale-scalar-tensor-normalization: the existing statement concerns "Underlying tensor normalization of pro-etale scalar and inverse-image comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-stratum-scalar-extension: the existing statement concerns "Stratum pullback and scalar-extension comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-sp-supported-etale-tensor-origin: the existing statement concerns "Bounded etale tensor origin for an open-supported finite-Tor complex"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-external-comparison-triangles: the existing statement concerns "Triangle compatibility of the external direct-image comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-fixed-stalk-identification-reduction: the existing statement concerns "Finite reduction of a fixed-point stalk identification"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-frobenius-coefficient-reduction-coherence: the existing statement concerns "Frobenius pullback comparisons commute with coefficient reduction"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-kv-evaluation-formula: the existing statement concerns "Evaluation of the canonical Künneth–Verdier map"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-nearby-compact-tensor-coherence: the existing statement concerns "Tensor and compact-support coherence before duality"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-nearby-geometric-slice: the existing statement concerns "Geometric specialization slices of the vanishing topos"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-space-section-algebra-etale-base-change: the existing statement concerns "The section algebra of a line module on a space restricts correctly to etale bases"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-trf-trace-map-from-external-duality: the existing statement concerns "Trace morphism from external duality"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-tw-ordinary-completed-integral-pullback: the existing statement concerns "Ordinary ringed pullback agrees with completed integral pullback on constructible complexes"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-boundary-proetale-projection-comparison: the existing statement concerns "Proper compact-support and tensor comparisons identify etale and pro-etale projection maps"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-closed-costalk-duality: the existing statement concerns "Exceptional restriction of a Verdier dual"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-constant-weil-structure-stage-independence: the existing statement concerns "The canonical Weil structure on the constant object is independent of the coefficient stage"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-etale-native-tensor-pullback: the existing statement concerns "Native unbounded derived tensor commutes with etale inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-finite-compact-projection-formula: the existing statement concerns "Finite-coefficient compact-support projection formula"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-integral-twist-base-change: the existing statement concerns "Completed integral twist lines commute with finite scalar base change"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-integral-twist-derived-scalar: the existing statement concerns "Twisting commutes with completed derived scalar extension"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-isomorphism-derived-pullback-reduction-tower: the existing statement concerns "Inverse-image relabelling identifies completed coefficient reduction towers"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-adic-flat-iff-supplied-model-flat: the existing statement concerns "Ambient and supplied-model Padic cohomology flatness"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: the existing statement concerns "Universality of the transported inverse-image pairing"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: the existing statement concerns "The canonical bilinear pairing of the specified inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: the existing statement concerns "The normalized tensor comparison for the specified algebraic inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-augmented-cech-tensor-pullback: the existing statement concerns "Augmented Cech tensor actions commute with derived inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-augmented-diagram-projection-mate: the existing statement concerns "Projection mate for an augmented coefficient diagram before taking inverse limit"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: the existing statement concerns "Construction of the normalized ordinary tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-compatible-finite-derived-trivializations: the existing statement concerns "Compatible trivializations of finite derived local systems"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-constant-completion-equivalence: the existing statement concerns "Constant-to-completed coefficients on derived-complete categories"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-constant-derived-normalization-universal: the existing statement concerns "Constant derived realization preserves universal coefficient arrows"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-continuous-module-encoding-lattices: the existing statement concerns "Local freeness and lattice compatibility of the explicit continuous encodings"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-continuous-module-encoding-restriction: the existing statement concerns "Continuous module encoding commutes with restriction along an etale morphism"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the existing statement concerns "Scalar extension under the continuous integral and rational module encodings"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-derived-adjunction-shift: the existing statement concerns "Canonical derived ringed-topos adjunction is shift-compatible"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation: the existing statement concerns "Derived morphism sheaves evaluate on weakly contractible pro-etale affines"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-derived-scalar-extension-local-systems: the existing statement concerns "Coherent localized derived scalar extension and comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-finite-reduction-pullback-coherence: the existing statement concerns "Finite reduction and the canonical pullback square"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the existing statement concerns "Derived pullback computes K-flat tensor representatives"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-left-exact-site-inverse-image-tensor: the existing statement concerns "Inverse image induced by a continuous left-exact site functor and its tensor structure"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-localization-inverse-image-coherence: the existing statement concerns "Coherent localization comparison for exact inverse image"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-module-pullback-tensor: the existing statement concerns "Pullback of modules commutes with tensor products, compatibly with sections"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: the existing statement concerns "Normalization-compatible evaluation of actual local Isom sheaves"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-normalized-derived-isomorphism-transport: the existing statement concerns "Universal normalization and evaluation of source-site local Isom sheaves"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-normalized-etale-origin-witnesses: the existing statement concerns "Compatible etale-origin witnesses for normalized finite-coefficient towers"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-normalized-origin-comparison-coherence: the existing statement concerns "Comparison reduction respects canonical scalar units and composition"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-profinite-point-pullback: the existing statement concerns "Geometric inverse image from the profinite point and its monoidal comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: the existing statement concerns "Canonical shifts and action units of the derived pullback tensor comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-pulled-reduction-normalization-comparison: the existing statement concerns "Successive quotient normalizations under the pulled reduction comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-reduction-pullback-derived-tower: the existing statement concerns "Normalized derived pullback of a strict coefficient reduction tower"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-resolving-representative-whiskering: the existing statement concerns "Restriction to resolving representatives is fully faithful"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the existing statement concerns "Common quotient reduction of the geometric scalar comparison"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-equivalence-module-hom: the existing statement concerns "Module and closed Hom transport under a ringed equivalence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing statement concerns "Projection-formula coherence for a square of ringed topoi"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-projection-mate-exact: the existing statement concerns "Exactness data for the ringed-topos projection mate"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-projection-restriction: the existing statement concerns "Localization comparisons for the ringed projection mate"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-slice-comparisons-shift: the existing statement concerns "Shift normalization of canonical ringed-slice comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing statement concerns "Slice restriction preserves evaluation for an arbitrary dualizing object"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-slice-koszul-coherence: the existing statement concerns "Normalized slice restriction preserves Koszul exchange"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing statement concerns "Existence of normalized slice tensor, Hom and Koszul comparisons"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-square-tensor-compatibility: the existing statement concerns "Tensor compatibility of a ringed square on flat K-flat representatives"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the existing statement concerns "Derived tensor comparison for arbitrary ringed topoi"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the existing statement concerns "Canonical tensor comparison unit existence"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the existing statement concerns "Canonical tensor comparison unit uniqueness"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: the existing statement concerns "Underived tensor comparison for pullback of modules on ringed topoi"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail: the existing statement concerns "Tensor comparison tail for scalar-extended inverse-image modules"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-scalar-extension-tensor-comparison: the existing statement concerns "Scalar extension preserves the normalized sheaf tensor"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-stratum-completion-unit-restriction: the existing statement concerns "Restriction and finite-stratum detection of the adic completion unit"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-pbc-tensor-comparison-descent-representatives: the existing statement concerns "Unique descent of tensor comparison from representatives"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-weil-stratum-ambient-hom: the existing statement concerns "Internal Hom from extension along a stratum"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-wf-constant-twist-coefficient-comparison: the existing statement concerns "Constant-line tensor and scalar Weil twist in the two coefficient models"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-wf-etale-cup-functoriality: the existing statement concerns "Functoriality of cup products in ordinary etale cohomology"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lem-zl-rational-realization-tensor-comparison: the existing statement concerns "Tensor compatibility of the raw rational continuous realization"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lemma-weil-pbc-completed-pullback-reduction: the existing statement concerns "Reduction commutes with completed pullback"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lemma-weil-pbc-koszul-quotient-limit: the existing statement concerns "Koszul and quotient towers have the same limit"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lemma-weil-pbc-projection-formula-finite-free: the existing statement concerns "Finite-free projection formula"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lemma-weil-pbc-projection-formula-totalization: the existing statement concerns "Signed totalization of the perfect formula"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs lemma-weil-pbc-projection-formula-tower-compatibility: the existing statement concerns "Projection formulas form a coefficient tower"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs prop-asd-smooth-base-change: the existing statement concerns "Arbitrary base change for smooth ambient duality"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs prop-base-linear: the existing statement concerns "P7: the transform is linear over the base"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs prop-sf-dualizable-hom: the existing statement concerns "Internal Hom through the coefficient dual"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs prop-weil-pbc-direct-image-limits: the existing statement concerns "Direct image, derived limits, and completeness"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs prop-weil-pbc-levelwise-truncations: the existing statement concerns "Levelwise truncations of the adic tower"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs sbc-thm-adic-smooth-base-change: the existing statement concerns "Adic smooth base change"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs thm-exc-explicit-preservation: the existing statement concerns "Preservation in the open and finite etale cases"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs thm-pur-cohomological-smoothness: the existing statement concerns "Cohomological smoothness of smooth morphisms"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs thm-pur-general-admissibility: the existing statement concerns "Preservation for an affine base, modulo the open-complement condition"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs thm-sf-hom-comparison-constructible: the existing statement concerns "Internal-Hom comparison for finite-Tor constructible inputs"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

lem-sfb-etale-stalk-total-tensor-comparison vs thm-trf-internal-hom-pullback: the existing statement concerns "Internal Hom versus pullback for a site-perfect first variable"; it does not give the canonical geometric-stalk comparison on arbitrary unbounded etale total tensor complexes with both the coprojection/germ formula and chain-map naturality.

## Original argument retained for the next workers

Original step 1:

Write $S$ for the geometric-stalk functor. By [prop-weil-pbc-geometric-stalks-exact], $S$ is exact on abelian sheaves. The same holds on $A_T$-modules: kernels, images and cokernels have their induced scalar actions, and the abelian stalk comparisons are $A$-linear. Thus $H^n(SC)=S H^n(C)$ for every complex, and $S$ preserves acyclicity and quasi-isomorphisms. For any $A$-module $M$, [def-kun-constant-sheaf] and [lem-weil-pbc-sheafification-geometric-stalk] give $S(\underline M)=M$: in the constant presheaf all transition maps are identities, and every pointed neighbourhood maps to $(T,\bar t)$, so the constant-diagram colimit is $M$. This is the canonical constant-germ map, hence is natural and $A$-linear; in particular $S(A_T)=A$. Finally, the constant presheaf of an acyclic module complex is sectionwise acyclic, and its sheafification is acyclic by both clauses of [lem-weil-pbc-site-r-module-presheaf-sheafification-exact]. Therefore termwise constant sheaves carry acyclic module complexes to acyclic sheaf complexes.

Original step 2:

For any two complexes $C,D$ of $A_T$-modules, form the canonical comparison $S(C\otimes_{A_T}D)\cong SC\otimes_A SD$ of ordinary total tensor complexes. In degree $n$, [lem-kun-stalks-commute-colimits] moves $S$ through $\bigoplus_{p+q=n}$, and clause (1) of [lem-pod-etale-stalk-tensor-scalar] identifies each summand $S(C^p\otimes_{A_T}D^q)$ with $S(C^p)\otimes_A S(D^q)$. The colimit statement applies to module sheaves as well: its abelian comparison is $A$-linear, since each coprojection commutes with scalar multiplication; the colimit inherits the action from these coprojections. The differential convention of [def-pc-tensor-complex-sheaves] is $d_C\otimes1+(-1)^p1\otimes d_D$ on a $(p,q)$ summand. Naturality of the ordinary tensor comparison identifies these two summand maps with $d_{SC}\otimes1+(-1)^p1\otimes d_{SD}$. The degreewise isomorphisms therefore form an isomorphism of complexes, natural in both chain maps. All sums are the small countable sums indexed by $p+q=n$; no total product or convergence assertion occurs.

Original step 3:

Let $P$ be any K-flat $A_T$-module complex, with K-flatness as in [def-pc-kflat-complex]. To test $SP$ against an arbitrary acyclic complex $E$ of ordinary $A$-modules, use Step 1 to see that $\underline E$ is acyclic. Then $P\otimes_{A_T}\underline E$ is acyclic by K-flatness (interchanging tensor factors by the signed symmetry if necessary). Its stalk is acyclic by Step 1 and is $SP\otimes_A E$ by Step 2 and $S\underline E=E$. This is precisely the test in [def-pc-module-kflat-complex], so $SP$ is K-flat. This constant-coefficient argument works for every acyclic $E$, without requiring boundedness or termwise flatness of $P$.

Original step 4:

Choose complexes $C,D$ representing $K,L$, and K-flat resolutions $P\to C$, $Q\to D$ supplied by [lem-kun-flat-resolution-existence]. We may use $P,Q$ as the representing complexes themselves, so [def-kun-derived-tensor] computes $K\otimes_{A_T}^{\mathbf L}L$ by $P\otimes_{A_T}Q$ (the identity of $P$ is a K-flat resolution). Step 1 shows that $SP\to SC$ and $SQ\to SD$ are quasi-isomorphisms, and Step 3 makes $SP,SQ$ K-flat. Thus these are K-flat representatives of $K_{\bar t},L_{\bar t}$ in the sense of [def-pc-module-kflat-complex], and their total tensor $SP\otimes_A SQ$ computes the right side. Localizing the chain isomorphism of Step 2 for $(P,Q)$ gives the asserted isomorphism. The left side is computed by $S(P\otimes_{A_T}Q)$ because the derived stalk is termwise exact.

Original step 5:

The isomorphism is canonical and natural after localization. On K-flat representatives its comparison is exactly the chain isomorphism of Step 2, which commutes with both chain maps. Changing the first K-flat model along a quasi-isomorphism gives an isomorphism of tensor complexes in the derived category by [lem-kun-derived-tensor-well-defined]; its stalk is again a quasi-isomorphism by Step 1. Use the two K-flat representatives from Step 4. On the module side the other fixed factor is then K-flat by Step 3, so its tensor functor preserves quasi-isomorphisms by [def-pc-module-kflat-complex]; the same applies when changing the second representative. On the site side the assertion for the second factor is again [lem-kun-derived-tensor-well-defined], with the factors interchanged. The computation of both bifunctors is [def-kun-derived-tensor]. The naturality squares of Step 2 therefore remain commuting squares when any such quasi-isomorphism is inverted. The canonical independence of the K-flat construction in [lem-kun-derived-tensor-well-defined], together with the localization description [def-weil-abstract-derived-category], identifies the comparisons from different resolutions: chain-map naturality extends to inverses and composites, which generate the localized morphisms. Hence the comparison is a natural isomorphism of the stated bifunctors. No step used a bound on the complexes, a finiteness assumption on $A$, or a Tor-amplitude assumption.

Original steps 1 and 2 are the arguments assigned to the two new statement-only nodes. The constant-complex K-flat test, choice of resolutions, and factor-wise quasi-isomorphism checks remain explicit in the parent. The existing site-derived-tensor-descent node supplies the full formal localization work. No part is replaced by an unsupported reference to a source proof.
