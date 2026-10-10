# lem-sc-finite-pushforward-locally-free

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-finite-pushforward-locally-free.json`: split item; no Mathlib exact match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-affine-flat-projective.json`: new statement-only node; Mathlib match `Module.Flat.projective_of_finitePresentation`.

## Attachments

None.

## WANTED

None.

## What was wrong

The imported item had no proof steps. Its source argument requires the affine finite-flat algebra criterion, standard-open trivialization of a finite projective module, and local constancy of rank; these are now explicit dependencies rather than an unstated appeal to the two Stacks tags.

## What I could not finish

Nothing.

## Review by K1

I read the item, its blueprint ancestor `lem-sc-finite-duality`, the source declarations in `WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean` (especially `isFiniteLocallyFree_pushforward` at lines 214-240), and the Stacks route at Tags 02KB and 04MH. I also read the existing DAG statements for finite-projective standard covers, affine tilde-Gamma correspondence, and locally constant finite-projective rank. Step 1 uses the new node exactly for the affine conclusion that the finite, finitely presented, flat algebra is finite projective. Step 2 uses the existing standard-cover statement for the free localizations and the affine correspondence statement for identifying the pushforward with the associated sheaf. Step 3 uses the existing rank statement exactly for local freeness at prime localizations and local constancy. I checked the zero algebra, the identity finite-flat map, a finite free algebra of rank one, and a disconnected base with different ranks on components. I recorded the Mathlib search for the new node and verified the candidate source line 287.
