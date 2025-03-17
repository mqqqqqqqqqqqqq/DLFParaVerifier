Program execution steps:

1. Starting the NuSMV server:

    ```cd /serverCe
    python3 server/server.py
    ```

2. Inductive invariants for obtaining agreements:

    ```
    python DLfree/auxinvPro.py
    ```

4. Verifying generalizability needs to be executed on a local VM with IVy, using the example of mutualEx:

    ```
    ivy_check mutualEx_prove.ivy
    ```



The <mark>auxiliary invariants</mark> generated by WiseParaVerifier are stored in `/protocols/mutualEx/mutualEx_invs.txt`.

The <mark>inductive invariants</mark> generated by the DLFVerifier are stored in `/protocols/mutualEx/mutualEx_prove.ivy`.



Notes on individual folders:

1. The WiseParaVerifier folder holds the source program for the WiseParaVerifier tool.

    invFinder.py i.e. the main program to find auxiliary invariants.
    concretedF.py contains rules and invariants for instantiation, and a rewritten interface for constructing deadlock-free formulas.

2. The source program for this job is in DLfree.

   auxinvPro.py contains the WiseParaVerifier interface for promoting and calling. WiseParaVerifier with parameters.

4. The protocols contain various protocols and invariants.

5. serverCe is the server side of NuSMV.

6. client.py is the client for NuSMV.

7. murphi.py and murphiparser.py are compilation and conversion programs.
