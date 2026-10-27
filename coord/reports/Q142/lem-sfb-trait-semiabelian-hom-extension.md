## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-semiabelian-hom-extension.json`: repaired item; statement unchanged and now has an independent four-step Néron-model proof. Mathlib search found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-neron-lft-existence.json`: new statement-only prerequisite; Mathlib search found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-generically-isomorphic-semiabelian-open-immersion.json`: new statement-only prerequisite; Mathlib search found no match.
- `citations.json`: verbatim quotes for every cited node in every item step.
- `searches.jsonl`: all searches run for the item and both new nodes, including the retained earlier item searches.
- `repair-history.md`: retained returned proof, report, citations, and search history for the repair audit.

Attachments: none.

WANTED: G. Faltings, “Finiteness Theorems for Abelian Varieties over Number Fields”, Arithmetic Geometry (1986), Chapter II §2 Lemma 1, printed pp.10–11, local file `literature/faltings-finiteness-theorems-abelian-varieties.pdf`, for the item’s historical source. The primary scan was read online at https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf; no source was downloaded or repository file changed.

WANTED: Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), 10.1 Definition 1 and 10.2 Theorem 2 (printed pp.289 and 297; scan PDF pp.296 and 304), for `lem-sfb-semiabelian-neron-lft-existence`. The primary scan was read online at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.

WANTED: Brian Conrad, *Semistable reduction for abelian varieties*, proof of Theorem 4.4, especially Corollary 3.3, Lemma 4.9 and the quasi-finite birational argument (printed pp.12–16), for `lem-sfb-generically-isomorphic-semiabelian-open-immersion`. The primary notes were read online at https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf.

## Repair of the returned delivery

The returned delivery identified C6 and D1/D2: the item and Q08’s `lem-sfb-semiabelian-trait-hom-extension` are the same theorem, and the two deliveries had become a dependency cycle. I removed the twin citation and did not alter Q08’s node, `merged_into`, or its callers. The item now has a genuine independent split. The maintainer still owns canonicalizing the same-day duplicate pair and repointing callers; this repair does not pretend that a duplicate merge is a proof.

The new Néron node is a broader ambient-model existence and smooth mapping-property statement, with a locally finite-type model. The new open-immersion node concerns an already given map and proves that it is an open immersion; it does not assert extension or construct a model. Thus neither new node restates the item or merely moves its conclusion into an unsplit node.

## Not duplicates

`lem-sfb-semiabelian-neron-lft-existence` vs `lem-sfb-trait-semiabelian-hom-extension`: the former constructs a Néron lft-model and represents all smooth generic morphisms; the latter extends maps between two prescribed finite-presentation models.

`lem-sfb-generically-isomorphic-semiabelian-open-immersion` vs `lem-sfb-trait-semiabelian-hom-extension`: the former assumes a map is already given and proves it is an open immersion into an arbitrary smooth separated target; the latter constructs and uniquely factors an extension.

`lem-sfb-generically-isomorphic-semiabelian-open-immersion` vs `lem-sfb-semiabelian-neron-lft-existence`: the former is a criterion for a supplied morphism; the latter is an existence and universal mapping-property theorem. Neither is a specialization of the other.

## Review by Q142

I reread the repaired item and both new node files, their cited definitions, and the source passages named above. The item hypotheses are unchanged: an arbitrary DVR, its fraction field and trait, smooth separated commutative finite-presentation group schemes, and semiabelian geometric fibres, with no completeness, excellence, or perfection assumption.

Step 1 first checks that (P=H_F) is smooth by the smooth-base-change clause of `lem-pc-proper-base-change`. The base-changed closed diagonal is closed, and finite presentation over the DVR gives finite type on the generic fibre by the displayed affine charts. The semiabelian-fibre predicate is exactly the cited definition restricted to generic geometric points. These checks supply the hypotheses of the new Néron existence node. Its quoted mapping property gives group homomorphisms (j:H	o N) and (f:G	o N), with (alpha j_F) the identity and (alpha f_F=v).

Step 2 applies the new open-immersion statement to (j). I checked every hypothesis against the node: (H) has finite presentation and semiabelian fibres, while the Néron model (N) is smooth and separated and need only be locally of finite type. The cited open-immersion definition justifies writing (U=j(H)) as an open subgroup of (N).

Step 3 uses the exact semiabelian geometric-fibre sequence and the integrality node at (n=1) to make each geometric fibre of (G) connected. Smoothness and finite type of those fibres were checked from the base-change statement and Step 1. The cited identity-component result makes (C=(N_Omega)^0) an open geometrically irreducible subgroup and stable under field extension. For every geometric point (x), the nonempty opens (U_Omegacap C) and its translate (x(U_Omegacap C)) intersect; writing an intersection point as (xz) proves (xin U_Omega). Hence the connected fibre image of (f) lies in (U), and the generic fibre lies there because (j_F) is an isomorphism. Since a trait has generic and closed points only, the image is contained in (U). The cited open-subscheme factorization then produces the unique scheme map (widetilde v:G	o H).

Step 4 uses that an open immersion is a monomorphism. Composing the multiplication, unit, and inverse identities with (j) proves that (widetilde v) is a group homomorphism. The Néron mapping-property bijection, applied to the smooth scheme (G), gives uniqueness after composing any competing extension with (j); monicity cancels (j). The same equations give (widetilde v_F=v).

I checked the Néron source’s local criterion against the new statement: geometrically semiabelian groups have no additive subgroup after the completed strict-henselian extension, so BLR’s lft existence theorem applies without assuming the DVR excellent or complete. I checked Conrad’s cited argument at Corollary 3.3 and Lemma 4.9; the open-immersion node records the extracted given-map argument and explicitly identifies it as an agent-written generalization, rather than claiming Conrad’s theorem has the exact broader statement. The Mathlib Birational hit was read and rejected because it proves only the reverse implication (an already dominant open immersion is birational); the FlatMono hit was likewise read and rejected because it requires flatness and monomorphism, which are conclusions here.

I tested edge cases conceptually: the zero group and zero homomorphism, rank-zero semiabelian fibres, split tori such as (mathbf G_m), and abelian schemes. The locally-finite-type qualification is necessary for a Néron model such as the component-rich model of (mathbf G_m). A non-semiabelian additive special fibre would invalidate the connected-fibre argument, which is why the semiabelian hypothesis is used explicitly. No SGA 4 or SGA 4½ source is cited. Every citation quote in `citations.json` was checked as a literal substring of the cited node statement, and every item step’s uses is included in `proof_deps`. All proof steps are under 2000 characters and contain no hidden separately stated lemma.

## Unfinished work

The two new prerequisites remain statement-only stage-1 nodes, as required. The maintainer must merge the duplicate Q08/Q142 item nodes and repoint callers after delivery; no worker-owned merge was attempted.

