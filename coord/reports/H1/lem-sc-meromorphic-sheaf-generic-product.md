Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-meromorphic-sheaf-generic-product.json` (repaired split)
- `dag/nodes/sec-abelian-varieties/lem-sc-meromorphic-weakass-generic-product.json` (statement-only, no Mathlib match)
- `dag/nodes/sec-abelian-varieties/lem-sc-ass-weakass-locally-noetherian.json` (statement-only, no Mathlib match)
- `citations.json`

Attachments: none.

WANTED: literature/stacks-project/divisors.tex, Tags 0EMF, 05AR and 0EMH; the repository stores the cited tag records but not the TeX source.

The returned version incorrectly quoted Tag 0EMH as the whole proof and did not use the no-embedded-points hypothesis. I followed the source route through Tag 0EMF, added the required statement-only 0EMF node and the Tag 05AR Ass=WeakAss node, and cited the existing Mathlib-backed nodes for Noetherian open subschemes and finite irreducible components. Step 2 now spells out why the generic local ring is Artinian and why every non-zero-divisor is a unit. Step 3 derives $(ft)_\eta=f_\eta t_\eta$ and restriction compatibility from the stalk definition.

## Review by H1

I read the item, its consumer `lem-sc-regular-meromorphic-section-exists`, the imported blueprint ancestor `lem-sc-hilbert-polynomial`, and the source locations for Tags 0EMF, 05AR and 0EMH recorded in the node. The new 0EMF statement includes both hypotheses required by its source, defines weakly associated points in the statement, and gives both products for a quasi-coherent module. The new 05AR statement records equality of associated and weakly associated points for a locally Noetherian scheme.

Step 1 uses exactly those two new statements, the existing node that an open subscheme of a Noetherian scheme is Noetherian, the existing finite-irreducible-components leaf, and then the 0EMF conclusion. I checked that the no-embedded-points hypothesis supplies the associated-point clause and that quasi-compact opens supply the finite-component clause. Step 2 uses only the stalk definition for the sheafified localization and writes the local-ring argument: primes are generalizations of the generic point, the maximal ideal is the nilradical, non-units are nilpotent zero-divisors, and the localization set consists of units. It also explicitly checks $j_\eta^{-1}(U)$ is either `Spec O_{X,eta}` or empty because a generic point has no proper generalization. Step 3 uses the 0EMF product statement and the verbatim stalk multiplication rule to obtain the module formula and restriction compatibility.

I checked edge cases of an empty open, a one-component integral scheme, and a zero-dimensional nonreduced generic stalk such as `Spec(k[epsilon]/(epsilon^2))`; the latter confirms why the argument must say non-zero-divisors are units rather than claim there are no zero-divisors. Every citation quote in `citations.json` is copied from the cited node statement. Mathlib searches for both new nodes were run with LeanFinder, Loogle and grep; LeanFinder found only unrelated declarations, Loogle was unavailable on the identifiers, and grep found no associated-point or meromorphic-sheaf API.

## Second reading by H1

- Item statement: checked against Divisors Tag 0EMH (`/home/ubuntu/c1-stacks-review/divisors.tex`, label `lemma-quasi-coherent-K`, lines 6315--6346); hypotheses and generic-point product conclusions agree.
- Step 1: checked against Tags 0EMF and 05AR and the cited Noetherian-open and finite-components nodes; the no-embedded-points implication and finite affine-cover argument supply both 0EMF hypotheses.
- Step 2: checked against Tag 0EMH's generic-stalk paragraph and the stalk definition; the zero-dimensional local-ring argument allows nilpotents and proves every non-zero-divisor is a unit.
- Step 3: checked against Tag 0EMF's quasi-coherent-module clause and the stalk multiplication rule; tensor, product, multiplication, and restriction compatibilities are derived.
- `lem-sc-meromorphic-weakass-generic-product`: checked against Tag 0EMF; retained as a strict supporting theorem.
- `lem-sc-ass-weakass-locally-noetherian`: checked against Tag 05AR; retained with the weak-association definition corrected to minimal over an annihilator.
- Changes: corrected both weak-association definitions, added the quasi-coherent definition dependency, repaired Step 1's locally Noetherian-to-Noetherian justification, and synchronized the affected citation quote.
- Edge cases: empty open, one-component integral scheme, and `Spec(k[epsilon]/(epsilon^2))` checked; source TeX was read locally from `/home/ubuntu/c1-stacks-review/divisors.tex`.
