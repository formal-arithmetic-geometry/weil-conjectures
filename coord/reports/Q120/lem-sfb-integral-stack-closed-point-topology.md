Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-stack-closed-point-topology.json` — split statement; no new nodes and no Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.
- `report.md` — this report.

Attachments:

- None. I searched the upstream source for the blueprint tag, declaration names and the stack/integral closed-point terminology; no sorry-free project declaration states this item.

WANTED:

- None. The proof uses the local Stacks sources already present in `literature/stacks-project/`.

What was wrong or changed:

- The imported item had an empty proof despite an assertion stronger than the usual scheme lemma: the source stack need not be finite type or Noetherian, and the morphism need not be surjective. I retained the statement and replaced the informal source sentence about finite stabilizer orbits by an explicit atlas and field-relation argument.
- I did not create a node that merely restates either conclusion. Existing nodes provide the reduced closed substack, its flat finitely presented field cover, stack topology, closed-immersion calculus, integral scheme closedness, integral incomparability, affine charts of quasi-compact algebraic spaces, finite-type-over-a-Noetherian-base, Noetherian space topology, and finite irreducible-component/generic-point facts.

What I could not finish:

- No Lean code was written or compiled, as required for stage 1.

## Not duplicates

- `lem-sfb-integral-stack-closed-point-topology` vs `lem-sfb-stack-point-topology`: the existing node defines the point-space topology and continuity; this item proves a closed-map and closed-fibre theorem for integral representable stack morphisms.
- `lem-sfb-integral-stack-closed-point-topology` vs `lem-sfb-stack-closed-immersion-calculus`: the existing node gives closed-immersion topology; this item applies it to the reduced singleton substack and proves the integral-fibre conclusion.
- `lem-sfb-integral-stack-closed-point-topology` vs `lem-sfb-singleton-stack-flat-lfp-field-cover`: the existing node constructs a field cover of a reduced singleton stack; this item uses that cover in the proof of closedness above a closed point.
- `lem-sfb-integral-stack-closed-point-topology` vs `lem-sfb-representable-stack-universally-closed-test`: the existing node characterizes universal closedness for representable stack maps; this item proves the assertion from integral base changes and additionally proves closedness of points in fibres.

## Review by Q120

I read the item node, its chapter and unit records, the current blueprint snapshot, and the cited Stacks passages. Step 1 uses the atlas quotient/topology and the scheme fact that integral morphisms are universally closed; the base-change image clause is exactly the one needed to identify the image of a closed subset after pulling it to the atlas. Step 2 uses the unique reduced closed substack supported at the closed point, closed-immersion local finite type, the locally-Noetherian finite-type chart lemma, and the existing flat locally finitely presented field-cover lemma. I checked that local Noetherianity is asserted only for the target singleton substack, never for the source.

Step 3 forms the integral scheme fibre over the field cover. The two projections are a base change of the field cover, so the point map is open and quotient. Integral incomparability says comparable primes with the same field contraction are equal, hence every point of this affine integral fibre is closed. Step 4 identifies the fibre of the quotient map over a chosen point with a field relation over the target stack. Quasi-compactness of the target diagonal gives a quasi-compact algebraic-space relation; the existing affine-etale-atlas lemma supplies an affine chart. Its map to the chosen residue field is locally of finite type, so the chart is Noetherian and has Noetherian topology. I checked the fibre-product identification directly from the triples defining a 2-fibre product and used the existing point-image/base-change statement.

Step 5 uses the finite irreducible-component theorem and the scheme sobriety theorem. A generic point specializes to every point of its component, while the image point in the integral fibre is closed; therefore each component has one image point, so the fibre over the selected point is finite and closed. Step 6 applies the quotient topology, then the closed-immersion topology, to conclude that every point over the closed target point is closed upstairs. Empty fibres are vacuous. I checked all hypotheses cited in these steps and copied each cited node's full statement verbatim into `citations.json`; the step dependency union equals `proof_deps`. Mathlib searches were run and recorded for the item; they found only scheme/ring generalizations, not this algebraic-stack statement. No statement was weakened, no SGA source was used, and no compiler or Lean build was run.
