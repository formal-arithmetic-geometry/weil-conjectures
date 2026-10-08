+++
id = "sec-nagata-compactification"
kind = "section"
title = "Nagata Compactification"
order = 0
+++
content: Every separated finite-type morphism to a quasi-compact,
quasi-separated scheme admits a compactification.  
key theorem: Thm [sk-thm-nagata-compactification]  
references: `nagata.svg`; `nagata_new.tex`;
Conrad, *Deligne's notes on Nagata compactifications*, §§1–2;
Stacks, [Nagata compactification](https://stacks.math.columbia.edu/tag/0F3T).

The dependency spine is the one in `nagata.svg`: Deligne–Conrad
elimination of indeterminacy gives compatible modifications; these prepare
two compactifiable opens for gluing; the two-open theorem gives the
Noetherian case; approximation then removes the Noetherian hypothesis.
We keep the boundary and valuative steps visible, since they are what make
the glued ambient scheme proper. Construction details and formalization status are recorded in
`nagata_new.tex`.
