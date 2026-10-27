## Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-tate-variable-roots-separable-compositum.json — item, split in eight steps, statement unchanged; added the previously missing algebraic-closure notion dependency.
- dag/nodes/sec-trace-formula/lem-trf-irreducible-separable-contraction.json — statement, Mathlib leaf Polynomial.exists_separable_of_irreducible (Mathlib/FieldTheory/Separable.lean:354–355).
- citations.json — one verbatim quotation for every step/node citation.

Attachments: none. Searches of lean/WeilConjectures/ by the item tag, Tate/restricted-series terminology, variable roots and separable compositum found no declaration proving all the item. FiniteRootedExtension concerns finite algebraically independent tuples and coefficient roots, not restricted series or this base enlargement; InseparableDegreeDrop proves a degree-drop statement, not the item.

WANTED: archival copy of Kiran S. Kedlaya, More on affinoid algebras, 18.727 fall 2004, https://kskedlaya.org/18.727/spectra2.pdf, Theorem 4 proof, PDF p.2, part (a), for lem-trf-tate-variable-roots-separable-compositum. Read online; not downloaded or written into the repository. Its variable-root argument treats the purely inseparable case. The preparation for a general finite extension, including its embedding and separability, is an agent-written elaboration, explicitly marked as such.

The imported statement was mathematically correct. It omitted the algebraic-closure definition from stmt_deps; this is added without changing its statement. Its warning that F need not be perfect is essential. Nothing is unfinished in this one-level split; the new node is a searched, statement-only Mathlib leaf.

The current blueprint ancestor and unit have been read in literature/blueprint/latest/, as have the chapter/unit records. Their current contracting-correspondence route does not contain this analytic preparation verbatim. The item's existing blueprint provenance explicitly identifies this as the historical Temkin/affinoid normalization supporting branch. This delivery refines only that existing analytic item, and does not change either the current unit or chapter route. The blueprint ancestor is lem-trf-local-term-locality, obtained with tools/blueprint_refs.py ancestor; the new node's via starts with this item and retains the ancestor chain. Whole-blueprint searches for variable-root, restricted series, irreducible polynomial, separable contraction, Frobenius expansion and formal power series found no node stating the new contraction fact. Broader purely-inseparable and Frobenius results were read where relevant.

## Searches and reuse

All Mathlib queries were run through the prescribed msearch.py and are retained in searches.jsonl; mathlib_searches copies their tool, exact query, actual returned result object and verdict. No service was unavailable. Two formulations of the whole Tate/fraction-field claim returned only abstract field results and restricted-series definitions, not a one-line specialization. The contraction search finds an exact positive match in the first phrasing; the full local declaration at Separable.lean:354–377 was read. The formal-series searches found map_iterateFrobenius_expand and map_frobenius_expand, whose full local declarations at Expand.lean:233–256 and coefficient formulas at 103–137 were read.

A second whole-DAG declaration search found the existing lem-weil-pbc-power-series-frobenius-coefficientwise. I removed the uncommitted proposed iterated-Frobenius node and used that existing leaf, spelling out its induction in step 4. The other reused generic statements are lem-weil-pbc-power-series-domain, lem-trf-irreducible-separable-derivative, lem-sfb-separable-generated-scalar-extension and lem-trf-finite-domain-fraction-degree. None requires a new copy. The first and the separability-generation criterion are existing Mathlib leaves, so they do not replace any unit route. All cited statements were opened, rather than relying on their source tags or proofs.

## Not duplicates

lem-trf-irreducible-separable-contraction vs lem-trf-irreducible-separable-derivative: the existing node only characterizes separability by a nonzero derivative; it explicitly excludes the positive-characteristic expansion which the new leaf supplies.

lem-trf-irreducible-separable-contraction vs lem-trf-separable-monic-approximation: the existing node constructs nearby separable monic polynomials in a valued field, not an exact Frobenius expansion of a given irreducible polynomial.

lem-trf-irreducible-separable-contraction vs lem-trf-polynomial-constant-shifts-finite-exceptions: the existing node bounds exceptional constant shifts when the derivative is nonzero; it does not contract an inseparable polynomial.

lem-trf-irreducible-separable-contraction vs lem-sfb-dvr-completion-extension-approximation: the existing node descends finite extensions of a completed DVR fraction field and requires a specified separable/root compositum; it supplies no irreducible-polynomial contraction.

lem-trf-irreducible-separable-contraction vs lem-sfb-padic-minpoly-normed-separation: the existing node concerns characteristic-zero p-adic minimal polynomials, their norms and root separation; the new leaf concerns positive characteristic over arbitrary fields.

lem-trf-irreducible-separable-contraction vs lem-sfb-tame-galois-curve-normalization-smooth: the existing node gives residue separability and smoothness for tame curve normalizations, not polynomial contraction.

lem-trf-irreducible-separable-contraction vs lem-sfb-norm-algcl-internal-hom-base-change: the existing node compares derived internal Hom under coefficient extension; its polynomial source tag is not a statement of contraction.

lem-trf-irreducible-separable-contraction vs lem-per-char-zero-smooth-coefficient-system: the existing node writes a characteristic-zero field as a union of smooth coefficient subrings; it does not concern positive-characteristic polynomials.

lem-trf-irreducible-separable-contraction vs lem-per-minpoly-iterated-frobenius: the existing leaf computes the minimal polynomial of a power of an already separable element; it assumes separability and cannot supply the contraction of an inseparable minimal polynomial.

lem-trf-irreducible-separable-contraction vs lem-weil-pbc-finite-fraction-root-substitution: the existing node roots finitely many rational functions by a coefficient extension and polynomial-variable substitution; it does not produce a separable contraction of an irreducible polynomial.

## Review by NK

I read Kedlaya's Theorem 4 on PDF p.2, especially the passage adjoining p-power roots of Tate variables in (a). It justifies the chosen analytic strategy, but not all the general finite-extension conclusion. I therefore kept the agent attribution, and supplied the missing field algebra rather than treating the handout as stating this stronger preparation. For the new contraction leaf I read Stacks fields.tex, lemma-irreducible-polynomials, Tag 09H0, including its induction which removes exponents divisible by p, and the exact Mathlib theorem at Separable.lean:354–355. Its hypotheses are a field of positive characteristic and an irreducible polynomial; neither monicity nor perfectness is needed. The separable polynomial convention was checked against def-pc-separable-polynomial: it is a Bezout identity with the formal derivative, not merely a nonzero derivative.

Step 1 cites the actual domain assertion of lem-weil-pbc-power-series-domain. Passing to the restricted subring preserves 1 and zero products. The restricted-subring definition is precisely def-trf-restricted-series-presentation. Finite-dimensionality supplies a basis and the displayed dependence of powers, and def-weil-pbc-separable-algebraic-extension supplies the monic irreducible minimal polynomial and its kernel-generator characterization. These are exactly the properties used later, not properties extracted from a node's proof.

Step 2 applies the derivative criterion only to irreducible minimal polynomials. In characteristic zero their positive degree has nonzero image in F, so the leading derivative coefficient cannot vanish. In characteristic p the new node says exactly f_i(Z)=g_i(Z^(p^m_i)) with g_i separable; this is the expression the step uses. Constants inject, so the characteristics of K, T and F agree. Taking the maximum is justified by the finite basis; no claim of perfection of F occurs.

Step 3 is an elementary coefficient calculation using the two cited series definitions. Every coefficient convolution is finite. Each multi-index has exactly one quotient/remainder decomposition modulo q, giving both spanning and linear independence. Restricting to a residue class retains only a subset of the coefficients above any fixed positive bound; hence the coefficient subseries are restricted. This verifies the topology condition in the actual definition, rather than an unrestricted formal-series assertion. The basis is a finite set of q^d monomials including the empty monomial when d=0.

Step 4 uses the existing formal Frobenius coefficient identity exactly as stated and iterates it e times (base e=0 is the identity; each successor multiplies exponents and raises coefficients by p). Algebraic closedness of K, from def-weil-algebraic-closure, supplies coefficient roots; def-weil-ring-frobenius supplies the ring identities. The threshold equivalence |c^(1/q)|>=epsilon iff |c|>=epsilon^q checks the analytic point which a purely formal calculation would miss. The coefficient map theta need not be K-linear; the proof only uses it as a ring isomorphism. Its extension to fractions is given by an explicit formula and cross multiplication, and theta(iota_q(x))=x^q is the compatibility subsequently needed.

Step 5 checks existence in the specified Omega, not an unspecified overfield. The only cited inputs are algebraic closedness and Frobenius identities, and the step writes out the uniqueness and ring-map arguments. The image is all q-roots of F because theta is surjective, so every smaller p-power root needed in step 6 lies in this same image E. The construction sends an original x in F to that same x in Omega.

Step 6 is an elementary polynomial calculation: the unique coefficient-root map is a ring embedding. It sends the actual Bezout identity to a Bezout identity because formal differentiation commutes with coefficient maps. The displayed q_i-power equation annihilates a_i. I checked that h_i is nonzero and nonconstant: coefficient injectivity preserves its degree, and g_i is nonconstant since f_i is. The minimal polynomial therefore exists and divides h_i by the kernel-generator clause already quoted. The explicit product-derivative identity proves its separability; no unsupported assertion that nonzero derivative alone implies separability is used. This step uses only the cited definitions plus the previous root construction, with its algebra written out.

Step 7 cites the final clause of lem-sfb-separable-generated-scalar-extension, which actually says that a field generated by separable algebraic elements is separable algebraic. Both its base fields are E and the ambient field is Omega; its hypotheses allow this identity base enlargement. It supplies all elements of the compositum, not just separability of the chosen generators.

Step 8 cites lem-trf-finite-domain-fraction-degree only after constructing S as a finite E-module domain. Closure under multiplication follows from the original basis multiplication constants in F, hence in E. The fraction field of S is exactly EL by the two inclusions spelled out in the step. Thus the cited finite-domain lemma supplies finiteness without assuming the tensor product is a field, or claiming the original F-basis remains linearly independent over E.

I checked B–E against the saved node files: the new node is statement-only, self-contained TeX and an exact Mathlib match, with from.place/via and logged searches; all shared-tag candidates above are different statements. The citations file copies the exact statements for every use, including each definition. The split is not a new lemma restating the whole conclusion: the only new node is the generic irreducible-polynomial theorem, while all Tate structure, embeddings and assembly remain in the item. All step texts are below 2000 characters. The proposed formal Frobenius leaf was corrected to reuse an existing one before delivery. No target statement, Lean source, chapter/unit file, repository or launcher file was written.

Small cases checked: q=1 and e=0 give renaming, identity coefficient maps and basis {1}; d=0 gives T=K, with all algebraic generators already in algebraically closed K. If L=F, all generator exponents can be zero. For L=F(X_1^(1/p^s)) in positive characteristic, q=p^s absorbs that generator into E, so the resulting degree-one extension is separable. A separable nontrivial extension also permits q=1. Constants with norm bigger than 1 cause no difficulty because the root threshold calculation uses every positive epsilon. No unproved perfectness claim, completeness of the fraction fields, or restriction on separable degree enters the argument.
