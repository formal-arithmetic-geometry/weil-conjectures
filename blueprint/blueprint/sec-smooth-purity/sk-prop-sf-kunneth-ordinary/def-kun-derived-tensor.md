+++
id = "def-kun-derived-tensor"
kind = "definition"
title = "Derived tensor product of etale sheaves"
order = 1683
uses = ["def-kun-constant-sheaf", "def-weil-pbc-etale-site"]
+++
Let $\Lambda$ be a commutative ring and $T$ a scheme, and work on
the small etale site of $T$, [def-weil-pbc-etale-site], with
sheaves of $\Lambda_T$-modules. A complex $\mathcal E^\bullet$ of
$\Lambda_T$-modules is *K-flat* if
$\mathcal E^\bullet\otimes_\Lambda\mathcal F^\bullet$ is acyclic for
every acyclic complex $\mathcal F^\bullet$. The *derived tensor
product* of $K_1,K_2\in D(T_{\Et},\Lambda)$ is

$$
K_1\kunotimes{\Lambda}K_2=P\otimes_\Lambda K_2
\in D(T_{\Et},\Lambda),
$$

where $P\to K_1$ is a quasi-isomorphism with $P$ K-flat; the
independence of the result of the chosen K-flat model is
recorded with the other properties of this construction. For $K\in D(T_{\Et})$ and a complex of $\mathbf Z$-modules
$\mathcal M^\bullet$, $K\kunotimes{\mathbf Z}\underline{\mathcal M^\bullet}$
denotes derived tensor with the constant complex of
[def-kun-constant-sheaf].
