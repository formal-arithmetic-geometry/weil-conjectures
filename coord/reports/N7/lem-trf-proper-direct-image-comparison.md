# Files written

- `lem-trf-proper-direct-image-comparison.json`: split into six proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node and step.

# Attachments

None. No exact sorry-free declaration for this item exists in `WeilConjectures/` of slopmaster2 or the upstream master reference.

# WANTED

None. Varshavsky's paper is present locally and supplies §4.1.4(a).

# Problems found

The imported node was unsplit and had an empty proof. Its statement agrees with Varshavsky §4.1.4(a) after translating the paper's correspondence notation to the project's coefficient-pushforward and fixed-diagram conventions. The proof now makes the seven requirements explicit. The only generic inputs beyond the item's original statement dependencies are the existing finite six-functor package and Nagata compactification/extension nodes; these are declared as tool uses. No duplicate node was created, and no statement was weakened or strengthened.

# Unfinished

No unfinished stage-1 work remains in this sandbox. The required dry run is still to be run.

## Review by N7

I read the item statement and its imported dependencies `def-trf-coefficient-conventions`, `def-trf-coefficient-pushforward`, `def-trf-cohomological-comparison`, `lem-trf-fixed-map-proper`, and `def-trf-admissibility`. The coefficient conventions establish the finite-Tor constructible categories; the pushforward node supplies the proper maps, commutation relations, and induced fixed map; the fixed-map lemma supplies properness of the fixed map and product map; and admissibility supplies the ordinary and exceptional adjunctions used by all mates. I also read `def-trf-kernel-pushforward-maps` for the exact lax tensor multiplication formula, `prop-functor-package` for composition, proper `*=!`, and Verdier exchange, and the two Nagata nodes used in the compactification step.

Step 1 checks every hypothesis: p and q are proper, the relations are exactly b_i q = p c_i, and p_F is proper by the fixed-map lemma. It defines the comparison maps by the specified adjunction mates and explicitly records that no leg square is assumed Cartesian. Step 2 checks the tensor map, symmetry, associativity, and the coefficient unit against requirements (I) and (II), using counit naturality and triangle identities. Step 3 checks identity and composite ordinary mates and the tensor exchange against requirement (III) and (IV), with the composite relation p_W h g = bar h bar g p_U. Step 4 uses the package's Verdier exchange isomorphism and proper *=! identification to verify that the evaluation-defined map d_Z is invertible, exactly requirement (V). Step 5 checks proper direct-image composition and exceptional conjugation, so the two mates are inverse as required by (VI). Step 6 constructs compactifications and extensions of p and q using Nagata and Conrad's extension theorem; on the proper compactified diagrams Steps 2–5 apply, and restriction gives the comparison isomorphisms required by (VII).

I tested edge cases in the statement: the identity proper diagram gives identity comparisons; empty schemes and zero complexes give zero functors with the same formulas; p and q may be proper while X,Y,C,B are nonproper over k; and no Cartesian leg square is used. The Mathlib searches found only generic sheaf pushforward and proper-map declarations, so the item is not a Mathlib leaf. All search commands and their outputs are recorded by the launcher search log.

## Second reading by N7

- Item statement: checked against Varshavsky §4.1.3(a), §4.1.4(a), and the current statements of `def-trf-coefficient-conventions`, `def-trf-coefficient-pushforward`, `def-trf-cohomological-comparison`, `lem-trf-fixed-map-proper`, and `def-trf-admissibility`; verdict: the correspondence legs, properness hypotheses, induced fixed map, exchange orientations, evaluation duality map, seven requirements, and absence of Cartesian/proper-over-$k$ assumptions agree.
- Step 1: checked the induced maps on $X$, $X\times X$, $C$, $F$, and $s$ against the proper-pushforward and fixed-map statements, and checked the ordinary and exceptional mate definitions; verdict: all $p_Z$ are explicitly identified as proper and the exchange construction is typed.
- Step 2: checked the adjoint tensor formula against the multiplication clause of `def-trf-kernel-pushforward-maps`, the finite-Tor tensor conventions, and the unit/counit triangles; verdict: commutativity, associativity, and the coefficient-unit identity give (I)--(II) with no hidden construction.
- Step 3: checked the composite relation and pullback compositor against `def-trf-cohomological-comparison`, proper direct-image composition in `prop-functor-package`, and the ordinary adjunction; verdict: identity/composition and tensor compatibility give (III)--(IV), including non-Cartesian leg squares.
- Step 4: checked the evaluation mate against the dual-pushforward/trace-counit construction, the Verdier exchange clause of `prop-functor-package`, and requirement (V); verdict: the inverse Verdier exchange is identified with $d_Z$ by mate uniqueness and is an isomorphism.
- Step 5: checked both mates against the proper composition and exceptional-adjunction statements and requirement (VI); verdict: the direct-image comparison is invertible and its exceptional conjugate is its inverse.
- Step 6: checked the compactification order against Varshavsky Remark 1.1.3 and §4.1.4(a), Nagata, and Conrad extension; verdict: the closure of the joint $(q,c)$ map lies in the separated equalizer, supplies compatible $q^*,c^*$, and restriction supplies (VII).
- New nodes: none; no duplicate, elementary, restatement, or Mathlib-leaf node was introduced.
- Edge cases: checked the identity proper diagram, zero complexes, empty schemes, a field coefficient stage ($n=1$), the excluded $n=0$ case (the coefficient convention requires $n\ge1$), and nonproper-over-$k$ schemes with proper $p,q$; verdict: the statement and formulas remain well-typed, with $n=0$ correctly outside the hypotheses.
- Searches and citations: reread the worker's recorded LeanSearch/LeanFinder/Loogle/grep results and verified every citation quote against the current shared node statements; no Mathlib declaration matches this geometric comparison.

Changes made: corrected the item's `created` provenance to this delivery, added the explicit tensor definition as a statement dependency, added missing package/kernel/cohomological citations to the relevant steps, made all induced proper maps and the evaluation mate explicit, and replaced the vague final compactification paragraph by the closure-in-the-separated-equalizer construction from §4.1.4(a). No statement clause was weakened or strengthened, and no new node was needed.

## Dry run result

`python3 /home/ubuntu/weil-launcher-nt/deliver.py N7 lem-trf-proper-direct-image-comparison --no-push .` passed at `ec944b87ae`: preflight passed (`OK (not pushed)`).
