# Worker report

1. Files written:
   - `dag/nodes/sec-fourier-transform/lem-fd-cohomology-affine-line-character.json`: item, statement; six proof steps, status split; no Mathlib match.
   - `dag/nodes/sec-fourier-transform/lem-fd-finite-etale-adic-cohomology.json`: one new statement-only node, status unsplit; no Mathlib match. It supplies finite-etale adic direct image, its Leray comparison and its exchange with pullback. There are zero Mathlib leaves.
   - `citations.json`: verbatim statements for all step citations.
2. Attachments: none. The named source theorem is not an attachment. Its actual hypotheses are a finite coefficient domain, a finite base field, a primitive character, and an algebraically closed extension. It relies on `isZero_cohomology_affineLine_artinSchreierSheafOf` (lines 97–103) and `cohomology_affineLine_unit` (lines 67–80), both sorry in the current read-only source. It does not give the item's adic algebraically closed coefficient statement. The theorem at lines 108–137 has a sorry-free wrapper, which does not close these inputs.
3. WANTED: none. The blueprint proof and the Stacks finite-coefficient source are present. The adic extension is an agent-formulated auxiliary statement; it is not claimed as a verbatim Stacks theorem.
4. Faults found: the characteristic and nontrivial character were left implicit, the notation over algebraically closed fields did not specify a sheaf construction, the rational finite-pushforward comparison was justified only by a torsion statement, the statement dependencies were empty, and the original proof was one long paragraph. See the source-error and review sections below.
5. Nothing in the assigned split remains unfinished. The new child is deliberately unsplit, as required for a one-level split. No Lean was written and no compiler, Lake or build tool was run.

## Source error

STATEMENT-DISPUTED: read without the chapter conventions, the imported assertion is not well-defined: it permits algebraically closed fields of characteristic zero, where the characteristic-p Artin–Schreier construction used in its proof does not apply, and does not specify the nontrivial character. For the trivial character and k=F_2, a=1, the sheaf is constant and H^0 is Qbar_l, contradicting the asserted vanishing. In characteristic p, a general additive group character on an algebraically closed field is not by itself the specified algebraic Artin–Schreier local system, and there is no finite field trace from that field to F_p.

The correction makes the chapter's intended data explicit: distinct primes p and ell, a fixed nontrivial character of F_p, and k finite or algebraically closed of characteristic p. It defines the sheaf by the prime-field Artin–Schreier construction. For finite k, the conventional notation psi=Psi composed with Tr_(k/F_p) is retained; for algebraically closed k it is sheaf notation. No vanishing case in the intended positive-characteristic setting is removed. The cohomological index is explicitly nonnegative. The formula itself is unchanged.

There is also a coefficient-domain gap in the source proof: `lem-fd-finite-pushforward-cohomology` states its identity for torsion etale sheaves only. It cannot directly be applied to Qbar_l in the adic category. The new child supplies the needed adic assertion and deck-equivariance. The unit's cover/decomposition/scaling route stays intact.

## Sources and search results

I read the chapter record `sec-fourier-transform`, unit record `sk-lem-as-properties`, the current main-20261015 statement, its separate `.proof.md`, the current unit's `.proof.md`, and the older master node containing the same proof. The current definition `sk-def-as` allows the finite field F_p and defines the sheaf of f as a pullback. Using this prime-field instance keeps the unit's explicitly specified cover T^p-T=f. I did not replace it by the q-power cover without a comparison.

For the child, I read Stacks `etale-cohomology.tex`, Proposition `proposition-finite-higher-direct-image-zero`, Tag 03QP, including its two clauses (finite stalk products, vanishing of positive direct images), and Lemma `lemma-finite-pushforward-commutes-with-base-change`, Tag 0959, including its stalk comparison proof. The former is the finite-level foundation, not a claim that Stacks already proves the adic extension. To split this child later one can use finite etale local splitting (direct image is a finite product of sheet restrictions), compatible finite-level exactness and exchange, derived-complete integral realization, and common-stage rational scalar extension; the identity Gamma_X f_*=Gamma_Y then gives the derived comparison. Naturality in deck maps must be retained at each stage. This is a general finite-cover coefficient lemma, not the affine-line character vanishing restated.

I searched the entire DAG for Artin–Schreier, finite direct image, finite etale cohomology, adic/rational pushforward, the source declaration names and Tag 03QP. I ran `tools/blueprint_refs.py search` for Artin, finite pushforward, finite direct image, Leray, finite etale adic, 03QP, and finite pushforward base change; its ancestor command identifies the item itself. No blueprint node states the combined adic assertion. The existing Leray and finite-pushforward nodes are discrete torsion/abelian statements; `prop-exc-finite-etale-adjoint` has finite coefficients. The completed coefficient comparison is useful infrastructure, not this whole finite-etale statement. No duplicate was created for isomorphism invariance, finite sums, the eigenvector calculation, or the trivial torsor calculation.

All Mathlib searches are actual msearch.py invocations preserved in searches.jsonl. The searches used both phrasings of the character vanishing and the finite-etale comparison, natural-language search, Loogle, and local Mathlib grep. The first LeanSearch call was rate-limited and is recorded unavailable. The successful LeanSearch finite-etale query found generic pushforward-composition and structural-sheaf facts; they do not supply adic constructible coefficients or this Leray comparison. LeanFinder's character queries found group/cotangent cohomology, not etale cohomology. Its finite-cover query found generic site and sheaf pushforward facts. The Loogle IsRightAdjoint hits only assert adjoint existence; none identifies the functor or its exactness here. I read Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean lines 19–85: `ellAdicSheaf` and `EllAdicCohomology` define the constant integral cohomology, and only empty-scheme vanishing is present. They are not a one-line specialization proving either statement. No positive match is claimed.

## Review by Q59

I checked B–E with the statements and the sources open. The child introduces all schemes, coefficient rings, normalized free lisse systems and their realizations; it has no proof or proof dependencies. Its notions are either explained inline or carried by actual definition dependencies. I distinguished the completed/integral and rational stages from discrete non-torsion small-etale sheaves. Source tags 03QP and 0959 were read in the local .tex and checked against the tags file, not guessed section numbers. All formulas use single TeX escapes in the decoded JSON. The child's from.node is the blueprint item itself, and from.place names the coefficient comparison it serves; same_as is empty after the whole-blueprint searches.

Step 1 uses the explicit y^p-y equation and translations in `lem-fd-as-cover-affine-line`, the finite etale torsor assertion in `lem-fd-as-cover`, and the isotypic decomposition of `lem-fd-as-characters`. The pullback definition is exactly in `sk-def-as`. The new child's exchange, including compatibility with character idempotents, justifies pulling that prime-field definition to K; the character/projector identification is not taken from an uncited proof. Choosing E containing mu_p is legitimate since it is a finite algebraic extension of Q_l; p is a unit in O_E and character values are roots of unity, so the projectors preserve the integral lattice. No primitivity over an arbitrary finite coefficient ring is presumed.

Step 2 uses exactly the child's ordinary cohomology isomorphism and its deck-equivariance clause. Its schemes are affine lines, hence noetherian of dimension one, and ell is invertible because char(K)=p is distinct from ell. The coefficient system is constant and finite free at each finite level. I did not use the torsion-only node to make a rational-coefficient assertion.

Step 3 uses the full positive-degree vanishing clause of `lem-fd-affine-line-constant-cohomology`; the finite direct-sum argument is written out through inclusions and projections rather than citing additivity as an unstated theorem. It uses the cover comparison already established in Step 2, not the proof of a dependency.

Step 4 uses the degree-zero constant-section clause of that same constant-cohomology node. The constant section 1 is nonzero at y=0 and spans the one-dimensional H^0, so this identifies all sections as constants using the statement alone. Translation fixes the actual constant sections, which is stronger than merely saying an automorphism preserves the isomorphism class of the constant sheaf. The split inclusion from Step 3 embeds the character component. The argument (Psi(b)-1)v=0, with a nonzero invertible scalar, explicitly proves that component vanishes. Nontriviality of Psi is used precisely here; the result would fail for the trivial character.

Step 5 is elementary relative to the preceding steps and `sk-def-as`: the inverse scaling, substituted covering ring and unchanged deck maps are explicit. The site equivalence is just relabeling by mutually inverse scheme isomorphisms; it preserves terminal objects and resolutions, including coefficient systems, so there is no separate unstated comparison theorem. In particular a need not lie in F_p. This avoids the invalid shortcut that all nonzero a index summands of one fixed p-sheeted cover.

Step 6 uses the child's exchange to identify the zero pullback with the split torsor character summand, the actual pullback/isotypic definition in `sk-def-as`, and both degree clauses of the constant-cohomology node. The eigenfunction equation v(b+c)=Psi(c)v(b) has the explicitly written solution v(b)=Psi(b)v(0); this proves constancy without assuming it from lisseness or multiplicativity alone. The proof works also for p=2. The final formula follows by the exhaustive a=0/a!=0 split.

Small cases: k=F_2, ell odd, a=0 gives the constant degree-zero group; a=1 gives the nontrivial eigencomponent and its zero cohomology. If k is larger and a is outside F_p, multiplication by a remains an automorphism, so the argument still applies. If k is already algebraically closed, K=k and the geometric base-extension step is harmless. For the new child, an identity map gives the identity comparison; a split cover gives a finite product/sum of the original complexes; the empty cover gives zero on both sides, and rank zero is allowed. Varying sheet rank across components is interpreted locally. There is no compact-support assertion (which would have a different answer), no weight statement, and no purity or forbidden SGA route in this split.

The recorded lean_audit is stale against the supplied checkout: it reports the main declaration at 269–300 and its only open input as `nonempty_iso_rightDerivedLowerStar_affineLine`. The current source instead places it at 108–137 and calls the two sorry lemmas described above. I therefore did not manufacture an attachment or an unused child from an obsolete call graph. I also read the relative affine-line theorem at Purity/Smooth/AffineLine.lean lines 101–111: it is sorry. The existing `prop-pur-gm-relative-kummer` clause (1) records the relative acyclicity in the coefficient datum A_(E,n); it is a relevant existing node, but not an exact attachment of the more general finite-ring Lean signature. No audit fields were overwritten and no source coefficient mismatch was silently identified.

The corrections after self-review were to expose the finite-etale base-change clause (needed by the pullback definition), to cover noetherian finite-dimensional schemes so the prime-field-to-K square satisfies its hypotheses, and to cite it explicitly in both the coordinate and zero cases. All six steps are shorter than 2000 characters. Their only child is the genuine coefficient-comparison fact, not an affine-line vanishing clause. The report contains no claim of a completed Lean proof. The unit key node is not this item, so no unit record is edited.

## Not duplicates

lem-fd-finite-etale-adic-cohomology vs lem-fd-finite-pushforward-cohomology: the existing comparison is for torsion etale sheaves; the new assertion includes completed integral, rational and algebraically closed adic coefficients, compatible systems, exchange and deck-equivariance.
lem-fd-finite-etale-adic-cohomology vs prop-exc-finite-etale-adjoint: the latter gives finite-coefficient pro-etale exactness and adjunction, whereas the new assertion supplies the integral/rational realizations and their ordinary global-section comparison.

lem-fd-finite-etale-adic-cohomology vs lem-sbc-closed-coefficient-source-transition-iso: the existing statement identifies the source transition under a closed coefficient immersion in a smooth-base-change square; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-sbc-closed-coefficient-target-transition-iso: the existing statement identifies the target transition under a closed coefficient immersion in a smooth-base-change square; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs sk-lem-geo-finite-boundary: the existing statement detects constructibility or an isomorphism using an open part and a proper pushforward at finite coefficients; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-a1-finite-weil-sections-decomposition: the existing statement decomposes sections on a finite scheme into Frobenius orbits, rather than transporting adic cohomology along a cover; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-pushforward-unit-edge-compatibility: the existing statement proves a unit/edge-map naturality equation for discrete abelian sheaves; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-split-pieces-cofinal: the existing statement constructs cofinal finite split neighbourhoods or their section product diagram; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs sk-lem-pbc-finite: the existing statement states stalk products, exactness and exchange for ordinary discrete etale coefficients, without completed/rational coefficient systems; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-surjective-unit-mono: the existing statement asserts only monomorphy of the discrete pullback unit under a finite surjection; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective: the existing statement describes finite pushforward stalks or pointed-neighbourhood set-valued comparisons; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite: the existing statement describes finite pushforward stalks or pointed-neighbourhood set-valued comparisons; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs g1-finite-pushforward-pullback-comparison: the existing statement compares pullback bijectivity for torsion curve coefficient pairs; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-pushforward-cohomology: the existing statement states the edge comparison for ordinary abelian etale sheaves, not completed/rational adic realizations; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-split-sections-product: the existing statement constructs cofinal finite split neighbourhoods or their section product diagram; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-stalk-formula-restriction: the existing statement identifies the discrete geometric stalk product and its restriction maps; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-sets-finite-pushforward-stalk: the existing statement describes finite pushforward stalks or pointed-neighbourhood set-valued comparisons; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs g1-finite-pushforward-cohomology-comparison: the existing statement compares ordinary cohomology only for torsion curve coefficient pairs; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-finite-split-neighbourhoods-cofinal: the existing statement constructs cofinal finite split neighbourhoods or their section product diagram; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs g1-finite-pushforward-coefficient-control: the existing statement reflects primary torsion and constructibility, rather than identifying adic derived global sections; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the existing statement describes finite pushforward stalks or pointed-neighbourhood set-valued comparisons; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: the existing statement concerns field embeddings of finite extensions of a separably closed field; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-curve-assertions-dense-open: the existing statement relates the eight torsion curve assertions across a dense open; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-weil-pbc-curve-assertions-finite-pushforward: the existing statement transfers the eight torsion curve assertions across a finite morphism; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs lem-asd-supported-kummer-scalar-source: the existing statement compares supported finite-coefficient Kummer objects along a closed immersion; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

lem-fd-finite-etale-adic-cohomology vs sk-lem-curve-finite-support: the existing statement treats classical sheaves on curves and finite support, not the adic coefficient-system comparison; it does not assert the integral/rational adic coefficient-system Leray and base-change comparison.

The first required dry run exited successfully (OK, receipt 559cf110b9). After reading the final searches, I recorded their exact queries and clarified Step 4 that the nonzero section 1 spans H^0; I then reran the required dry run before pushing.
