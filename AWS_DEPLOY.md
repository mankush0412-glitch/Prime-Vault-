# AWS (EC2) deploy

1. Region: pick the one closest to your MongoDB (Atlas ap-south-1 / Mumbai is a good match). Mongo and the bot in
   different regions is the #1 cause of a slow bot. Instance: t3.small or bigger (t3.micro is tight with many sessions).
2. Security group: allow SSH (22). Open 8080 (or 80/443 via nginx) ONLY if you use the Razorpay webhook.
   Razorpay API polling needs no inbound port.
3. Install Docker, upload the project, create `.env` from `.env.example`, then:
       docker compose up -d --build
       docker compose logs -f
4. Update later:  docker compose up -d --build
5. Stop cleanly: `docker compose stop` (SIGTERM → the bot closes Server 2 / Server 3 connections).
6. Atlas: add the EC2 public IP in Network Access.
