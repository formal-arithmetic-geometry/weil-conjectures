# Repair of det-uniform-constructible-ext-integral

## Files written

- dag/nodes/sec-six-functors-basics/det-uniform-constructible-ext-integral.json: statement unchanged; short assembly of two comparison lemmas, the existing torsion bound and Milnor sequence.
- dag/nodes/sec-six-functors-basics/lem-sfb-lattice-supported-hom-reduction-tower.json: statement; unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-lattice-supported-hom-finite-comparison.json: statement; unsplit; no Mathlib match.
- citations.json: verbatim statement extracts for every assembly citation.

## Attachments

None. The project declaration AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtIntegral, lean/Sheaf/Paper/UniformConstructibleExtIntegral.lean:74, ends in sorry. Searches of lean/WeilConjectures for the blueprint tag, the notion and the declaration name found no finished declaration stating the item or either new comparison.

## WANTED

None. The current blueprint and the Stacks source used here are present.

## What was wrong and what changed

This is the human's deliberate stage-1 re-split, not a stale assignment. The live proof contains 4887 characters across six steps. The sandbox initially contained only dispatcher .brief files, not the delivered JSON, report or searches, so the current live item (including its original proof, citations, searches, Lean record and reviews) was the available returned version. Its statement and all unrelated fields are retained. No git command was run in the shared repository, and no Lean was edited or compiled.

The reconstruction argument formerly in steps 1–3 is now the independent first node; the coefficient-category and reduced-dual comparison formerly in steps 4–5 is now the independent second node. Both new nodes are statement-only, status unsplit, with empty proof and proof_deps. They can be worked on independently: neither depends on the other or on the item. The first supplies no vanishing bound; the second supplies no inverse-limit reconstruction and no vanishing bound. Thus neither restates the item or any clause of its conclusion. The parent still explicitly applies the torsion bound and performs the Milnor computation.

Every original argument is preserved below as handoff material. The source reduction of Q, which appeared in original step 1 but was used in step 4, belongs to the finite-comparison node; the target reduction, completeness, dual finite-freeness, Roos-triangle and sections arguments belong to the tower node. The finite-comparison statement allows an arbitrary finite-coefficient target Kbar, because the old scalar-adjunction and support calculation never used a lattice presentation of that target. Apply it to b_!(M_0/pi^n) in the assembly.

## Sources and blueprint route

I read the chapter sec-six-functors-basics and unit sk-lem-uniform-constructible-ext records, the current main-20261015 unit proof (Lattices, Torsion targets and Integral targets), and the item's own blueprint statement. The route remains support-Hom, finite reduction, torsion bound, derived inverse limit. I also read the statements of sk-lem-integral-models (especially 2 and 4), sk-def-pe-derived-completion, sk-lem-formal-closed-support-ii, sk-lem-formal-closed-support (2), sk-def-sfb-coefficient-change, det-uniform-constructible-ext-torsion (2), lem-kun-site-rgamma-derived-limit and lem-pc-derived-limit-milnor-sequence.

For the tower node, the primary source is the blueprint's Lattices paragraph and the Integral targets paragraph through the displayed RHom/limit comparison. Stacks Tag 0D6K, sites-cohomology.tex, label lemma-RGamma-commutes-with-Rlim, was read in the local source: it states commutation of ringed-site derived sections with Rlim and the associated short exact sequences. The source reduction and completeness statements used by this extracted argument are actually present in sk-lem-integral-models (2),(4); the support/tensor sequential-limit assertions are actually in sk-lem-formal-closed-support-ii. The finite locally free dual is obtained by dual finite bases with inverse-transpose transition matrices.

For the finite-comparison node, I read the same blueprint's Torsion targets display and Integral targets paragraph, and the coefficient-change statement. The source's implicit coefficient comparison is expanded via the derived extension/restriction adjunction, not an identification of integral support with support in the quotient coefficient category. sk-def-sfb-coefficient-change states that adjunction for arbitrary coefficient morphisms. sk-lem-integral-models (4) gives the source reduction; sk-lem-formal-closed-support (2) applies to the reduced finite locally free lattice. In a finite local basis the reduced evaluation pairing is the dot product, and the inverse-transpose transition matrices agree, so the dual identifications glue. All those details remain in the original handoff text below.

For the final parent step I read Stacks Tag 07KY, more-algebra.tex, label lemma-break-long-exact-sequence, as well as the exact statement of lem-pc-derived-limit-milnor-sequence. This is the D(Ab) sequence needed after global sections. The original blueprint's section reference 08TB is not substituted for the precise lemma label.

## Searches and reuse

I searched the whole DAG by supported Hom, reduction, derived completeness, RHom/limit, and the Stacks tag; ran blueprint_refs.py ancestor and whole-blueprint searches for integral Ext, reduction Hom, derived complete Hom, coefficient adjunction, Hom limit, support limit, Ext restriction, dual reduction, lattice Hom and supported cohomology. The ancestor for both new nodes is det-uniform-constructible-ext-integral with via []. Neither comparison is an existing blueprint statement, so same_as remains []. Nearby generic statements were opened and compared, including det-lem-int-ext-formula, det-formal-closed-support-ii-limits, the internal-Hom continuity lemmas, lem-sfb-closed-supported-scalar-comparison, lem-coef-integral-hom-reduction and lem-sf-integral-hom-roos-transport.

All new Mathlib searches were run through the prescribed msearch.py, including LeanSearch, Loogle, LeanFinder, grep and a second natural-language phrasing for each node. I read their output. The tower searches returned generic derived-category/triangle declarations, ordinary condensed colimits and unrelated ordinary limits; precise grep for RHom/derivedHom/homotopyLimit/derivedLimit/Roos in Algebra/Homology returned no hits. The finite-comparison searches returned ordinary dual bases, algebraic local cohomology, ordinary module scalar operations and unrelated adjunction extensionality lemmas. None has the combined module-sheaf scalar/support assertion or specializes to all its clauses in one line. Exact queries and the actual reported hits are in each node's mathlib_searches and searches.jsonl; asynchronous completion order is handled by matching query text, not by assigning a range of log lines to a node. No service failure is represented as a negative mathematical result. The item's inherited searches are retained unchanged.

## Not duplicates

lem-sfb-lattice-supported-hom-reduction-tower vs lem-pod-connected-constant-h0: Its claim identifies degree-zero sections of constant coefficients on connected schemes, whereas this node reconstructs supported global Hom in all degrees for arbitrary lattice extensions.

lem-sfb-lattice-supported-hom-reduction-tower vs det-proper-heart-bound-lattice: Its conclusion is a proper-fibre cohomology vanishing bound; this node supplies the integral supported Hom tower without any proper morphism or bound.

lem-sfb-lattice-supported-hom-reduction-tower vs det-uniform-constructible-ext-integral: The item concludes Ext vanishing; this node supplies only reconstruction and tower/cohomology identifications, and uses no vanishing statement.

lem-sfb-lattice-supported-hom-reduction-tower vs lem-kun-site-truncation-derived-limit: It reconstructs a complex from lower truncations under a local vanishing assumption, not from lattice quotient targets through supported Hom.

lem-sfb-lattice-supported-hom-reduction-tower vs lem-zl-affine-curve-range: Its assertion is compact-support vanishing on affine curves; this node is a lattice supported-Hom comparison without a curve assumption or vanishing conclusion.

lem-sfb-lattice-supported-hom-reduction-tower vs prop-coef-integral-dualizing: It constructs the integral dualizing object and its representing formula over an algebraic closure of a finite field, not a Hom tower for two arbitrary lattice extensions over any k in the standing setting.

lem-sfb-lattice-supported-hom-reduction-tower vs lem-kun-0bkz: It identifies hypercohomology with sections of cohomology under local acyclicity; this node instead constructs the supported Hom quotient tower.

lem-sfb-lattice-supported-hom-reduction-tower vs lem-kun-site-rgamma-derived-limit: It only transports an already-given Roos triangle through sections; this node supplies the lattice reductions, completeness, support/tensor transport and global-Hom identification needed before that application.

lem-sfb-lattice-supported-hom-reduction-tower vs sk-lem-formal-closed-support-ii: It asserts sequential-limit preservation of individual support and tensor functors, not the lattice completeness and global Hom reconstruction asserted here.

lem-sfb-lattice-supported-hom-reduction-tower vs det-lem-int-ext-formula: Its supported Hom formula and finite-dual limit preservation do not identify lattice quotient targets or reconstruct the global Hom reduction tower.

lem-sfb-lattice-supported-hom-finite-comparison vs sk-def-sfb-coefficient-change: It gives the generic coefficient adjunction, not the source reduction, reduced-dual identification and finite supported-cohomology comparison.

lem-sfb-lattice-supported-hom-finite-comparison vs sk-lem-formal-closed-support: It gives the supported Hom formula within one coefficient category; the new node compares integral Hom into a restricted finite target with that finite-category formula.

lem-sfb-lattice-supported-hom-finite-comparison vs sk-lem-integral-models: Its lattice reduction assertion does not provide the scalar-adjunction and support-Hom comparison.

lem-sfb-lattice-supported-hom-finite-comparison vs lem-coef-integral-hom-reduction: It is a comparison for derived internal Hom reduced on both entries, not the global Hom groups into a restricted quotient target and their stratum support formula.

lem-sfb-lattice-supported-hom-finite-comparison vs lem-sfb-closed-supported-scalar-comparison: It proves the explicit scalar/closed-pushforward supported-unit comparison, not the global supported-Hom comparison into a quotient target.

lem-sfb-lattice-supported-hom-finite-comparison vs lem-pur-supported-hom: It has constant source i_*A_Z and bounded-below finite targets, not a locally closed integral lisse source with arbitrary finite derived target and quotient scalar comparison.

lem-sfb-lattice-supported-hom-finite-comparison vs det-uniform-constructible-ext-torsion: Its conclusion is cohomological support and vanishing for a finite target, whereas this node only identifies the integral morphism group with that finite supported-cohomology group.

## Review by Q76

I checked the returned instruction as a requirement to create real independent work, not just shorten prose. The new statements preserve the actual intermediate objects and outputs of the old argument. The tower statement deliberately uses integral support on Res(Nbar_n); the finite-comparison statement deliberately uses finite-coefficient support. Their equality is needed only on global cohomology groups and is obtained by scalar adjunction. This avoids assuming the two module categories or their support functors are identical.

For assembly step 1 I opened the new tower statement and checked that it gives both H^q(B_n)=Hom(Q,N_n[q]) and Ext^q(Q,N)=H^q(Rlim B_n) in D(Ab). Its hypotheses are precisely the given separated finite-type setting, the specified open/closed factorizations and finite locally free lattices. No properness, flat quotient map or Mittag-Leffler condition has been added. The termwise restrictions and quotient transitions are specified. The small-site hypothesis of the sections theorem is met by the explicitly chosen universe, and n>=1 is reindexed by n=m+1 when applying its n>=0 statement.

For assembly step 2 I read the entire finite-comparison statement against its use: its first group is exactly Hom(Q,Res(Nbar_n)[q]), its last group is exactly the finite support cohomology in torsion clause (2). Nbar_n is an object of D(A_{n,X}); finite freeness of the reduced source and reduced dual, admissibility of A_n, and the source derived-reduction comparison are explicit conclusions of this new statement. Applying the torsion statement at the same n uses its original lattices L_0,M_0 and the same immersions. Thus every non-elementary comparison this step needs is a cited statement. I did not cite the coefficient definition as if it alone proved the whole comparison; that argument is now a separately assigned theorem.

For assembly step 3 I checked that the cited Milnor statement is in D(Ab), not a sheaf category, and that its i can be q. For q>c+1 both q and q-1 are above c. The end towers are zero, including their first derived limit (the zero tower has a zero injective resolution), so exactness kills the middle. This is a short elementary consequence of the cited exact sequence and is retained explicitly. The one remaining non-elementary input is the cited Milnor sequence itself. The index shift n=m+1 is harmless. Infinite cohomological dimension gives an empty asserted range, exactly as the unchanged statement intends. Every cited statement fragment is copied verbatim to citations.json.

I checked B1–B10: both new nodes have no proof sketch in their statements and no proof steps, introduce all objects, name definitions for coefficients/lisse lattices/derived categories/tensor/direct images/sites through the cited nodes, use single-escaped TeX, have precise blueprint source places (and 0D6K label where used), have genuine logged searches, no false Mathlib leaf and correct blueprint provenance. I checked C1–C8: every assembly theorem is cited for its statement, not its proof; citations have the actual coefficient categories, no cyclic back-edge is introduced, and the only new parent off-unit tool is the already-used D(Ab) Milnor lemma declared in split_report.tool_uses. New nodes inherit this unit. I checked D1–D5: the two arguments have distinct self-contained comparison statements, neither proves the bound by fiat, all details of the former proof are handed on below, and no circular claim or omitted standard comparison remains in the parent. I checked E1–E7 using the actual source objects: no new geometric hypothesis, no replacement source or target, and no unproved naturality assertion about cross-coefficient support is required.

Small cases: if L_0 has rank zero, both comparison sides are zero; likewise for the empty source stratum. Empty T or zero M_0 gives the zero target tower. For X=Z=S=Spec of a separably closed field and a,b identities, the assertions reduce to ordinary finite-free module scalar adjunction and completeness. At n=1 the finite coefficient calculation uses the residue field and has the same reduced evaluation pairing. The tower statement is a limit identity without an extra-degree conclusion, so it is consistent with constant or zero towers. The parent retains the strict cutoff and does not claim vanishing at the cutoff; infinite endpoints are vacuous. No statement dispute was found.

The parent proof has 1763 characters, below 3000, and no step exceeds 2000. The former 2390-character reconstruction argument and 1613-character coefficient/support comparison are now separate unsplit nodes. The retained 884-character Milnor computation is the elementary assembly using the already-existing Milnor statement. No original substantive argument was discarded.

## Argument handoff, preserved from the returned proof

The following is handoff material in this report, not a proof field of an unsplit node. It preserves the former argument in full so the next workers can recover the details as well as the new statements. Original step 1's source reduction of Q goes with the finite-comparison node; its target-reduction/completeness part and steps 2–3 go with the tower node. Steps 4–5's comparison and dual/admissibility checks go with the finite-comparison node; step 5's application of the torsion bound remains in the parent. Step 6 remains in the parent, with references renumbered.

### Original step 1

Use the standing scheme and coefficient setting of the unit, and write $R_Y=\mathcal O_{E,Y}$ and $A_{n,Y}=(\mathcal O_E/\pi_E^n)_Y$ for every scheme $Y$, with $n\geq1$. Put $Q=a_!L_0$, $N=b_!M_0$, and $\overline N_n=b_!(M_0/\pi_E^n)$ in $D(X_{\mathrm{proét}},A_n)$. In the integral category let $N_n=\operatorname{Res}_{R_X\to A_{n,X}}\overline N_n$. Clause (4) of [sk-lem-integral-models], applied separately to $a,L_0$ and to $b,M_0$, identifies $Q\otimes^{\mathrm L}_{R_X}A_{n,X}$ with $a_!(L_0/\pi_E^n)$ and the underlying integral reduction of $N$ with $N_n$. Clauses (2) and (4) also make $N$ derived complete. Hence [sk-def-pe-derived-completion] gives $N\simeq R\varprojlim_{n\geq1}N_n$, with the canonical quotient transitions. All occurrences of a finite-coefficient object in the integral category here and below mean termwise restriction of scalars.

Cited statements: sk-lem-integral-models, sk-def-pe-derived-completion.

### Original step 2

In the integral coefficient category define $T(K)=L_0^\vee\otimes_{R_S}u^*R\underline\Gamma_ZK$, $F=T(N)$ and $F_n=T(N_n)$. The dual $L_0^\vee$ is finite locally free: on a trivialization of $L_0$ it is the dual finite free module, and the inverse transpose transition matrices glue these local duals. By [sk-lem-formal-closed-support-ii], both $u^*R\underline\Gamma_Z$ and tensoring with this dual carry sequential derived-limit triangles to the corresponding triangles of their image sequences. Apply these two assertions successively to Step 1 to obtain $F\simeq R\varprojlim_nF_n$ in $D(S_{\mathrm{proét}},R_S)$. This defines $F_n$ using integral support; no change-of-coefficient assertion about derived support is being presumed.

Cited statements: sk-lem-formal-closed-support-ii.

### Original step 3

Clause (2) of [sk-lem-formal-closed-support] with $\Lambda=\mathcal O_E$ gives $R\operatorname{Hom}_{R_X}(Q,N)\simeq R\Gamma(S,F)$ and $R\operatorname{Hom}_{R_X}(Q,N_n)\simeq R\Gamma(S,F_n)$. Set $B_n=R\Gamma(S,F_n)$, forgetting the coefficient action so that $B_n\in D(\operatorname{Ab})$. Apply [lem-kun-site-rgamma-derived-limit] to the ringed site $(S_{\mathrm{proét}},R_S)$, its terminal object $S$, and the tower of Step 2; choose a universe in which this site is small and reindex $n=m+1$ to use $m\geq0$. It gives $R\Gamma(S,F)\simeq R\varprojlim_nB_n$ in $D(\operatorname{Ab})$. The underlying complexes compute the same cohomology groups. Thus $\Ext^q_{R_X}(Q,N)=H^q(R\varprojlim_nB_n)$ and $H^q(B_n)=\operatorname{Hom}_{D(R_X)}(Q,N_n[q])$, by the definitions of derived Hom and Ext.

Cited statements: sk-lem-formal-closed-support, lem-kun-site-rgamma-derived-limit.

### Original step 4

For each $n$, apply the derived extension/termwise restriction adjunction stated in [sk-def-sfb-coefficient-change] to the quotient morphism of condensed rings $\underline{\mathcal O_E}\to\mathcal O_E/\pi_E^n$. Together with the source reduction from [sk-lem-integral-models], this gives, for every integer $q$,
$$H^q(B_n)=\operatorname{Hom}_{D(R_X)}(Q,\operatorname{Res}\overline N_n[q])\cong\operatorname{Hom}_{D(A_{n,X})}(Q\otimes^{\mathrm L}_{R_X}A_{n,X},\overline N_n[q])=\Ext^q_{A_{n,X}}\bigl(a_!(L_0/\pi_E^n),b_!(M_0/\pi_E^n)\bigr).$$
The adjunction is for arbitrary coefficient morphisms; in particular it requires no flatness of $R_X\to A_{n,X}$. It compares groups in the two different module categories rather than identifying those categories.

Cited statements: sk-def-sfb-coefficient-change, sk-lem-integral-models.

### Original step 5

Use clause (2) of [sk-lem-formal-closed-support] over the admissible finite ring $A_n=\mathcal O_E/\pi_E^n$ to express the last group of Step 4 as
$$H^qR\Gamma\bigl(S,(L_0^\vee/\pi_E^n)\otimes_{A_{n,S}}u^*R\underline\Gamma_{Z,A_n}\,b_!(M_0/\pi_E^n)\bigr).$$
Indeed $(L_0/\pi_E^n)^\vee=L_0^\vee/\pi_E^n$: in a local finite basis both evaluation pairings are the dot product over $A_n$, and their inverse transpose transition matrices agree, so these identifications glue. The ring $A_n$ is finite and killed by a power of $\ell$, and the reduced source is finite locally free, as required by the support formula. Clause (2) of [det-uniform-constructible-ext-torsion] now gives $H^q(B_n)=0$ for $q>c$, uniformly in $n$, where $c=\operatorname{cd}_\ell(j)+\operatorname{cd}_\ell(S)+1$. In particular the torsion bound is applied in its own coefficient category.

Cited statements: sk-lem-formal-closed-support, det-uniform-constructible-ext-torsion.

### Original step 6

Apply [lem-pc-derived-limit-milnor-sequence] to the tower $B_n$ in $D(\operatorname{Ab})$ from Step 3. It gives
$$0\longrightarrow R^1\varprojlim_nH^{q-1}(B_n)\longrightarrow H^q(R\varprojlim_nB_n)\longrightarrow\varprojlim_nH^q(B_n)\longrightarrow0.$$
For $q>c+1$, both $q>c$ and $q-1>c$, so Step 5 makes each of the two towers in the end terms the zero tower. Their limit and first derived limit are zero (the zero object has the zero injective resolution), hence the middle group is zero by exactness. Step 3 identifies that group with $\Ext^q_{\mathcal O_E}(a_!L_0,b_!M_0)$. Since $c+1=\operatorname{cd}_\ell(j)+\operatorname{cd}_\ell(S)+2$, this is precisely the claimed bound. No surjectivity or Mittag-Leffler assumption on the cohomology towers is used. If a cohomological dimension is infinite the claimed range is empty, so only the finite-bound case needs this computation.

Cited statements: lem-pc-derived-limit-milnor-sequence.

## What remains

The two new comparison lemmas intentionally remain unsplit for parallel future work. Their statements are not Lean proofs. Stage 1 only; no further task is claimed.
