# Delivery report: `lem-weil-pbc-closed-immersion-residue-field-iso`

## Worker report

This is a repair of the returned delivery. Step 1 now follows the reviewed
pushforward-stalk route: the closed-immersion sheaf map is stalkwise
surjective, `lem-weil-pbc-closed-pushforward-stalks (2)` identifies the
pushforward stalk with `O_{Z,z}`, and the composite is explicitly the stalk
map `i^sharp_z`, which is local by
`def-weil-locally-ringed-space-morphism`. Step 2 takes the quotient by the two
maximal ideals and proves bijectivity. No new nodes were created.

## Review by F1

I checked the repaired step against the cited source locations: Morphisms
01QO supplies the closed-immersion sheaf surjection, while the Schemes
01HJ-area supplies the stalk and residue-field maps for a morphism of locally
ringed spaces. The node `lem-weil-pbc-closed-pushforward-stalks (2)` supplies
the bijection `c_z : (i_* O_Z)_x -> O_{Z,z}`. The node
`lem-weil-pbc-locally-surjective-iff-stalks` supplies surjectivity of the stalk
map, so the argument no longer hides either fact. The composite with `c_z` is
the germ definition of `i^sharp_z`; the cited locally-ringed-space definition
therefore justifies its locality.

For step 2, the residue-field definition gives `A/m_x -> B/m_z`. Surjectivity
comes from the preceding surjective local map, and its kernel is zero because a
local homomorphism has preimage of `m_z` equal to `m_x`. Hence the map in the
statement is an isomorphism. The `uses` lists and `proof_deps` agree exactly,
all cited nodes exist on the current `sheaf-dag`, and no source tag is used
without a cited node.

## Outstanding

No mathematical gaps remain in this repair. The delivery is based on the
current `sheaf-dag` tip and contains only the item JSON and this report.
