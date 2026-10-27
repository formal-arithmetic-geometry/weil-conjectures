# Stage-1 delivery: lem-per-semilinear-character-projector-lifting

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-semilinear-character-projector-lifting.json`: statement, now split in seven steps; no Mathlib match for the entire semilinear statement.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-character-fourier-kernel.json`: one new statement-only lemma, unsplit; scalar Fourier completeness for an arbitrary finite abelian group over a field with an embedded cyclic root group of the requisite order. No exact or one-line Mathlib match found.
- `citations.json`: one verbatim statement quote for each of the two step citations.
- `searches.jsonl`: actual searches recorded by the required launcher command. The item's original searches were preserved, with new searches appended from this session.

New nodes: 1. New Mathlib leaves: 0. Existing Mathlib leaf reused: `lem-weil-pbc-vector-space-basis-through-vector`.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for semilinear actions, eigenvector lifting, character projectors and simultaneous diagonalization found no declaration stating every clause of the item. The nearby project Artin–Schreier discussion is not this local-ring statement.

## WANTED

None. The actual source is available locally and was read.

## Problems found and changes

The incoming item has no proof and no split review. There was no earlier sandbox split to reuse. Its statement is correct, including for a nontrivial action on A, and is unchanged. No STATEMENT-DISPUTED issue arises. The source's diagonalization sentence is an omitted standard argument, not a proof to copy without further dependencies. The new scalar Fourier-kernel lemma exposes its non-elementary finite-character input; the averaging, quotient, directness and stable-line arguments remain written in the item's steps. The original statement already defines the quotient field inline, so the inherited scheme-residue-field definition is not used to assert an unquoted theorem about abstract local rings.

ILO VIII Lemma 5.3.5 (printed p.124, PDF p.130) explicitly averages parameters and completes the cotangent eigenvectors to a basis. I read both paragraphs, and the following 5.3.7 context on pp.124–125. The current blueprint ancestor and its proof were read under `literature/blueprint/latest/`: the inherited chain names the regular-local purity input as historical Step 3, whereas the current proof's duality/regular-local input occurs in Step 1. The report records this provenance without changing the unit or chapter. This supporting algebra is still the existing rigidification branch through VIII 5.3.5.

## Searches and Mathlib assessment

All new search entries were taken from actual `msearch.py` log records, with exactly the tool and query used. I read the returned signatures. The service was available for the recorded searches; the Loogle query `LinearIndependent.extend` returned an unknown-identifier diagnostic, which was discovery work and is not represented as a successful theorem match.

For the Fourier child I used two general natural-language phrasings, then the explicit finite Fourier formulation, an exact-name Loogle query for `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, and a grep for it, character separation, and `sum_hom_units`. I opened `Mathlib/GroupTheory/FiniteAbelian/Duality.lean` lines 44–97 and `Mathlib/RingTheory/IntegralDomain.lean` lines 183–235. The finite-character cardinality theorem and separation theorem assume enough roots for the group exponent; the sum theorem assumes a homomorphism and its nontriviality. None directly states the sum over characters valued in the prescribed abstract cyclic group C with an embedding in an arbitrary field. The comparison of cyclic-target characters with all relevant field-valued characters, or equivalently finite-abelian cyclic decomposition and its character count/separation argument, is real remaining work, so this child stays unsplit. `AddChar.sum_apply_eq_ite` is the complex-valued analogue, not a specialization to arbitrary residue characteristic.

For the item, the fresh semilinear searches again found `Representation.averageMap`; I read `Mathlib/RepresentationTheory/Invariants.lean` lines 123–148. That construction is for linear representations. It does not assert the entire local semilinear quotient decomposition and lifting statement. A second search phrasing and source grep were also run. Searches for commuting diagonalizable families yielded generalized eigenspace results, which are another possible ingredient and were not mistaken for the item.

Basis-extension searches found the existing node `lem-weil-pbc-vector-space-basis-through-vector`; I read its full statement and source match, then Mathlib `LinearAlgebra/Basis/VectorSpace.lean` lines 45–65 and `LinearAlgebra/LinearIndependent/Lemmas.lean` lines 771–796. There is consequently no new basis node.

Whole-DAG and whole-blueprint searches covered character orthogonality, simultaneous diagonalization, eigenvector bases, primitive roots, sums of characters, and independent-set basis extension, together with the exact candidate declaration names. The ancestor command reports `lem-per-artin-gabber-affine-curve`; the child records that node, the inherited via chain prefixed by the item, and the exact VIII 5.3.5 diagonalization input. No blueprint node states the arbitrary-field cyclic-target Fourier kernel; `same_as=[]` for both delivered nodes.

## Not duplicates

lem-per-finite-character-fourier-kernel vs lem-per-semilinear-character-projector-lifting: the new lemma is a scalar sum over a finite character group; it asserts no module action, quotient decomposition, basis completion or eigenvector lifting. The item's steps construct and analyze all these objects.

lem-per-finite-character-fourier-kernel vs lem-per-abelian-inert-rigidification-cover: the existing node constructs a strict inert equivariant etale cover of a geometric pair, using the local algebra; the child is a finite scalar identity and constructs no cover.

lem-per-finite-character-fourier-kernel vs lem-per-very-tame-boundary-quotient-cartier: the latter is a geometric Cartier/quotient statement using eigenparameters; it does not assert a Fourier kernel identity.

lem-per-finite-character-fourier-kernel vs lem-per-finite-character-annihilator-duality: the latter identifies annihilator subgroups for a finite abelian group; it states neither the cardinality of the whole character group nor a sum in an arbitrary field, and cannot simply be quoted for this Fourier identity.

lem-per-finite-character-fourier-kernel vs lem-fd-character-orthogonality: the latter sums one additive character over a finite field with Qbar_ell coefficients; the new lemma sums all cyclic-target characters of an arbitrary finite abelian group, at a fixed group element, in an arbitrary splitting field.

lem-per-finite-character-fourier-kernel vs lem-sfb-character-eigenspaces-independent: the latter concerns independence of weight spaces for affine group schemes over an algebraically closed field, not the scalar completeness identity over a possibly finite residue field.

lem-per-finite-character-fourier-kernel vs lem-sc-primitive-root: the existing node supplies roots over an algebraically closed field; the child assumes an embedded cyclic root group and asserts a character sum, with no algebraic-closure assumption.

## Review by Q31

I reviewed delivery-errors B through E against the written JSON, not just the imported dependency lists. The only new node introduces k, N, H, C, the embedding and the character set in its own statement. It has no proof or proof dependencies, no hidden proof sketch inside its statement, and an explicit field-definition dependency. Its source is ILO VIII 5.3.5, printed p.124; I read the source's diagonalization sentence and state expressly that the scalar Fourier identity is the worker's expansion of the standard input, not a quotation from ILO. The source and Mathlib candidates above are the actual material I read. No Stacks result or SGA source is used. The item retains its initial statement and imports, and no unrelated file, Lean file, repository state, or compiler has been touched.

For step 1 I checked the quotient action directly: changing a representative of a scalar has no effect because mM is in L, and the action on k is trivial. Unit differences exclude equality of distinct root powers before and after reduction. This proves exactly the order and faithful reduction needed in step 4; it does not assume A is a field or the action is A-linear. The N=1 case has no unit-difference conditions, and C is then the trivial group.

For step 2 I recomputed the substitution t=gh and the coefficient identity chi(g^{-1}t)^{-1}=chi(g)chi(t)^{-1}. The action fixes chi(h) because zeta is fixed, and fixes N^{-1} because it fixes integers and inverses. The preserved-submodule assertion follows term by term, not from an invalid claim of A-linearity. Applying the quotient map gives the displayed k-linear operator p_chi. This elementary calculation uses no external theorem. Step 3 computes all N summands of p_chi(v) when v is an eigenvector, proving the lifting conclusion verbatim; it also supplies the identity on the eigenspace needed later.

Step 4 cites only `lem-per-finite-character-fourier-kernel`. I opened the child and checked its exact displayed identity; the verbatim statement is in citations.json. Its hypotheses hold for k and the cyclic group C from step 1, with |H|=|C|=N and N nonzero in k. The finite double-sum computation yields the identity operator, hence spanning. It does not assume the module is semisimple or invoke an unrecorded diagonalization theorem.

Step 5 proves directness by applying the constructed p_chi to a finite relation. On V_psi its value is visibly a scalar multiple of the input and also lies in V_chi. The nonzero difference of distinct character values in the field forces that scalar multiple to vanish when the characters differ. The identity case is precisely step 3. Thus the stronger finite-relation assertion, not merely pairwise intersections, is established. Step 6 uses the finite identity decomposition on a stable line: at least one projected component is nonzero, remains in that line, and hence forces the original vector into one eigenspace. This avoids any unsupported assumption that an arbitrary residue-field character automatically lifts to A.

Step 7 cites `lem-weil-pbc-vector-space-basis-through-vector`, whose statement I read in full: it states extension of EVERY independent subset to a basis, not just the singleton suggested by its title. I apply it to each k-vector space V_chi, after partitioning the original independent list by the unique character established in step 6. It contains those vectors without rescaling. Spanning and independence of the union are explicitly reduced to steps 4 and 5. This existing node is a Mathlib leaf, so it is an available generic linear-algebra tool across units. Its exact statement is copied in citations.json. No other cited theorem is smuggled into a step; all remaining calculations are elementary and written out. There are no non-elementary steps longer than 2000 characters (indeed all seven steps are shorter than 800).

I tested the new Fourier statement on H=C=1 (the single summand is 1), cyclic H of order 2 over a field of odd characteristic (1+(-1)=0 away from the identity), and H=C2 x C2 with C cyclic of order 4 over F5 (four characters, separating each nonidentity element, zero sums). In characteristic dividing N its explicit nonvanishing hypothesis fails, so the bad modular case is excluded. For general truth, the future proof can decompose H as a product of cyclic groups of orders d_i with product N. Each d_i divides N, so a cyclic C of order N has exactly d_i elements killed by d_i; these give exactly product d_i=N characters, and detect every nonidentity element of H. For h not equal to 1, choose a detecting character psi and reindex chi by psi*chi; the sum S then satisfies S=iota(psi(h))^{-1} S, so S=0 in k. At h=1 it is N. This is the finite-character lemma left to split, rather than hidden inside the item's elementary steps.

For the item I also checked V=0, an empty prescribed list, the trivial group, and repeated characters among independent prescribed vectors. In the last case all those vectors are extended together within one eigenspace; they are not incorrectly treated as distinct-character lines. Nontrivial semilinearity on A causes no change to the argument because only fixed coefficients occur in averaging.

## Unfinished work

None for this one-level split. The new scalar lemma is deliberately statement-only and enters the stage-1 queue. Direct delivery validation follows with deliver.py --no-push, then the required push after it exits successfully.
